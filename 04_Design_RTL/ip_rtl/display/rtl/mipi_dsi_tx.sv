// -----------------------------------------------------------------------------
// File: mipi_dsi_tx.sv
// Description: MIPI DSI-2 Transmitter - D-PHY and Protocol Layer
// Author: YaoGuang SoC Design Team
// Date: 2026-01-18
// -----------------------------------------------------------------------------

`timescale 1ns/1ps

module mipi_dsi_tx (
    input  logic                                    pixel_clk,
    input  logic                                    rst_n,
    input  logic                                    pixel_valid,
    input  logic [11:0]                             pixel_data_r,
    input  logic [11:0]                             pixel_data_g,
    input  logic [11:0]                             pixel_data_b,
    input  logic                                    pixel_de,
    input  logic                                    pixel_hsync,
    input  logic                                    pixel_vsync,

    output logic                                    dsi_clk_p,
    output logic                                    dsi_clk_n,
    output logic [3:0]                             dsi_data_p,
    output logic [3:0]                             dsi_data_n,
    input  logic                                   dsi_te,
    output logic                                   dsi_rst_n
);

    // MIPI DSI-2 Parameters
    localparam integer NUM_DATA_LANES = 4;
    localparam integer BYTES_PER_PIXEL = 3; // RGB888

    // D-PHY Timing (1.5ns period = 666MHz for 45Gbps/l.ane)
    localparam integer DPHY_HSSETTLE = 85; // 85ns
    localparam integer DPHY_TCLK_PRE = 8;
    localparam integer DPHY_TCLK_POST = 60;

    // DSI Packet Types
    localparam [7:0] DSI_DCS_LONG_WRITE = 8'h29;
    localparam [7:0] DSI_DCS_SHORT_WRITE = 8'h15;
    localparam [7:0] DSI_DCS_READ = 8'h06;

    // Registers
    logic [7:0]                                     lane_data [0:3];
    logic [7:0]                                     pixel_byte [0:5];
    logic [7:0]                                     packet_header [0:2];
    logic [15:0]                                    word_count;
    logic                                           packet_start;
    logic                                           packet_end;

    // -------------------------------------------------------------------------
    // Pixel to Byte Conversion
    // -------------------------------------------------------------------------
    always_ff @(posedge pixel_clk or negedge rst_n) begin
        if (!rst_n) begin
            pixel_byte[0] <= 8'd0;
            pixel_byte[1] <= 8'd0;
            pixel_byte[2] <= 8'd0;
            pixel_byte[3] <= 8'd0;
            pixel_byte[4] <= 8'd0;
            pixel_byte[5] <= 8'd0;
        end else begin
            if (pixel_valid && pixel_de) begin
                // RGB888 -> 3 bytes per pixel
                pixel_byte[0] <= pixel_data_r[11:4];
                pixel_byte[1] <= pixel_data_r[3:0] << 4 | pixel_data_g[11:8];
                pixel_byte[2] <= pixel_data_g[7:0];
                pixel_byte[3] <= pixel_data_g[3:0] << 4 | pixel_data_b[11:8];
                pixel_byte[4] <= pixel_data_b[7:0];
                pixel_byte[5] <= 8'd0; // Padding
            end
        end
    end

    // -------------------------------------------------------------------------
    // DSI Packet Generator
    // -------------------------------------------------------------------------
    dsi_packetizer #(
        .NUM_LANES          (NUM_DATA_LANES)
    ) packet_gen (
        .pixel_clk          (pixel_clk),
        .rst_n              (rst_n),
        .pixel_byte         (pixel_byte),
        .pixel_valid        (pixel_valid),
        .de                 (pixel_de),
        .packet_start       (packet_start),
        .packet_end         (packet_end),
        .lane_data          (lane_data),
        .word_count         (word_count)
    );

    // -------------------------------------------------------------------------
    // D-PHY Lane Driver
    // -------------------------------------------------------------------------
    genvar i;
    generate
        for (i = 0; i < NUM_DATA_LANES; i++) begin: dphy_lane
            dphy_tx_lane #(
                .DATA_RATE       (4500000000) // 4.5 Gbps per lane
            ) lane_driver (
                .pixel_clk       (pixel_clk),
                .rst_n           (rst_n),
                .byte_in         (lane_data[i]),
                .hs_enable       (pixel_valid && pixel_de),
                .lp_data_p       (dsi_data_p[i]),
                .lp_data_n       (dsi_data_n[i])
            );
        end
    endgenerate

    // -------------------------------------------------------------------------
    // D-PHY Clock Lane
    // -------------------------------------------------------------------------
    dphy_clk_lane #(
        .DATA_RATE          (4500000000)
    ) clk_driver (
        .pixel_clk          (pixel_clk),
        .rst_n              (rst_n),
        .hs_enable          (pixel_valid && pixel_de),
        .lp_clk_p           (dsi_clk_p),
        .lp_clk_n           (dsi_clk_n)
    );

    // -------------------------------------------------------------------------
    // TE and Reset
    // -------------------------------------------------------------------------
    always_ff @(posedge pixel_clk or negedge rst_n) begin
        if (!rst_n) begin
            dsi_rst_n <= 1'b0;
        end else begin
            dsi_rst_n <= 1'b1;
        end
    end

endmodule

// -----------------------------------------------------------------------------
// File: dsi_packetizer.sv
// Description: DSI Packet Generator
// -----------------------------------------------------------------------------
module dsi_packetizer #(
    parameter integer NUM_LANES = 4
) (
    input  logic                                    pixel_clk,
    input  logic                                    rst_n,
    input  logic [7:0]                              pixel_byte [0:5],
    input  logic                                    pixel_valid,
    input  logic                                    de,
    output logic                                    packet_start,
    output logic                                    packet_end,
    output logic [7:0]                              lane_data [0:3],
    output logic [15:0]                             word_count
);

    // DSI Virtual Channel
    localparam [1:0] VC = 2'd0;

    // Packet Header Components
    logic [5:0]                                     data_type;
    logic [1:0]                                     virtual_channel;
    logic [15:0]                                    packet_length;
    logic [7:0]                                     ecc;

    // State Machine
    typedef enum logic [2:0] {
        IDLE        = 3'd0,
        HEADER      = 3'd1,
        PAYLOAD     = 3'd2,
        CHECKSUM    = 3'd3,
        FOOTER      = 3'd4
    } state_t;

    state_t                                         state_reg, state_next;
    logic [15:0]                                    byte_counter;

    // Calculate ECC for packet header
    function [7:0] calc_ecc;
        input [39:0] header_data;
        integer i, j;
        reg [7:0] ecc_reg;
        begin
            ecc_reg = 8'd0;
            // Simplified ECC calculation
            for (i = 0; i < 8; i++) begin
                for (j = 0; j < 40; j++) begin
                    if (header_data[j] && ((j + i) % 8 == 0)) begin
                        ecc_reg[i] = ecc_reg[i] ^ 1'b1;
                    end
                end
            end
            calc_ecc = ecc_reg;
        end
    endfunction

    // Calculate 16-bit Checksum
    function [15:0] calc_csum;
        input [7:0] payload [];
        integer i;
        reg [15:0] csum;
        begin
            csum = 16'd0;
            for (i = 0; i < payload.size; i++) begin
                csum = csum + payload[i];
            end
            calc_csum = csum;
        end
    endfunction

    // -------------------------------------------------------------------------
    // Packet Generation FSM
    // -------------------------------------------------------------------------
    always_ff @(posedge pixel_clk or negedge rst_n) begin
        if (!rst_n) begin
            state_reg <= IDLE;
            byte_counter <= 16'd0;
        end else begin
            state_reg <= state_next;
            byte_counter <= byte_counter;
        end
    end

    always_comb begin
        packet_start = 1'b0;
        packet_end = 1'b0;
        lane_data[0] = 8'd0;
        lane_data[1] = 8'd0;
        lane_data[2] = 8'd0;
        lane_data[3] = 8'd0;

        case (state_reg)
            IDLE: begin
                if (de) begin
                    data_type = 6'h2E; // DSI_RGB888
                    virtual_channel = VC;
                    packet_length = 16'd3; // 3 bytes per pixel
                    packet_start = 1'b1;
                    state_next = HEADER;
                end else begin
                    state_next = IDLE;
                end
            end

            HEADER: begin
                // Send Virtual Channel + Data Type
                lane_data[0] = {virtual_channel, data_type};
                state_next = PAYLOAD;
            end

            PAYLOAD: begin
                if (pixel_valid && de) begin
                    // Distribute pixel bytes across lanes
                    lane_data[0] = pixel_byte[0];
                    lane_data[1] = pixel_byte[1];
                    lane_data[2] = pixel_byte[2];
                    lane_data[3] = pixel_byte[3];
                end
                state_next = FOOTER;
            end

            FOOTER: begin
                if (!de) begin
                    packet_end = 1'b1;
                    state_next = IDLE;
                end else begin
                    state_next = PAYLOAD;
                end
            end

            default: state_next = IDLE;
        endcase
    end

    assign word_count = packet_length;

endmodule

// -----------------------------------------------------------------------------
// File: dphy_tx_lane.sv
// Description: D-PHY Data Lane Transmitter
// -----------------------------------------------------------------------------
module dphy_tx_lane #(
    parameter integer DATA_RATE = 4500000000
) (
    input  logic                                    pixel_clk,
    input  logic                                    rst_n,
    input  logic [7:0]                              byte_in,
    input  logic                                   hs_enable,
    output logic                                    lp_data_p,
    output logic                                    lp_data_n
);

    // D-PHY States
    typedef enum logic [1:0] {
        LP_00     = 2'b00,
        LP_01     = 2'b01,
        LP_11     = 2'b11,
        HS        = 2'b10
    } dphy_state_t;

    dphy_state_t                                    state_reg, state_next;
    logic [7:0]                                     shift_reg;
    integer                                         bit_count;

    always_ff @(posedge pixel_clk or negedge rst_n) begin
        if (!rst_n) begin
            state_reg <= LP_11;
            shift_reg <= 8'd0;
            bit_count <= 0;
        end else begin
            state_reg <= state_next;

            if (hs_enable) begin
                if (bit_count == 0) begin
                    shift_reg <= byte_in;
                    bit_count <= 7;
                end else begin
                    shift_reg <= {shift_reg[6:0], 1'b0};
                    bit_count <= bit_count - 1;
                end
            end
        end
    end

    always_comb begin
        case (state_reg)
            LP_11: begin
                lp_data_p = 1'b1;
                lp_data_n = 1'b1;
                if (hs_enable) begin
                    state_next = HS;
                end else begin
                    state_next = LP_11;
                end
            end

            HS: begin
                lp_data_p = shift_reg[7];
                lp_data_n = ~shift_reg[7];
                if (!hs_enable) begin
                    state_next = LP_11;
                end
            end

            default: begin
                lp_data_p = 1'b1;
                lp_data_n = 1'b1;
                state_next = LP_11;
            end
        endcase
    end

endmodule

// -----------------------------------------------------------------------------
// File: dphy_clk_lane.sv
// Description: D-PHY Clock Lane Transmitter
// -----------------------------------------------------------------------------
module dphy_clk_lane #(
    parameter integer DATA_RATE = 4500000000
) (
    input  logic                                    pixel_clk,
    input  logic                                    rst_n,
    input  logic                                   hs_enable,
    output logic                                    lp_clk_p,
    output logic                                    lp_clk_n
);

    always_comb begin
        if (hs_enable) begin
            // HS mode: DDR clock
            lp_clk_p = pixel_clk;
            lp_clk_n = ~pixel_clk;
        end else begin
            // LP mode: static line state
            lp_clk_p = 1'b1;
            lp_clk_n = 1'b1;
        end
    end

endmodule
