// -----------------------------------------------------------------------------
// File: dp_tx.sv
// Description: DisplayPort 1.4a Transmitter - Main Link Encoder
// Author: YaoGuang SoC Design Team
// Date: 2026-01-18
// -----------------------------------------------------------------------------

`timescale 1ns/1ps

module dp_tx (
    input  logic                                    pixel_clk,
    input  logic                                    rst_n,
    input  logic                                    pixel_valid,
    input  logic [11:0]                             pixel_data_r,
    input  logic [11:0]                             pixel_data_g,
    input  logic [11:0]                             pixel_data_b,
    input  logic                                    pixel_de,
    input  logic                                    pixel_hsync,
    input  logic                                    pixel_vsync,

    output logic [3:0]                             dp_tx_data_p,
    output logic [3:0]                             dp_tx_data_n,
    output logic                                    dp_tx_clk_p,
    output logic                                    dp_tx_clk_n,
    input  logic                                   dp_hpd,
    inout  logic                                   dp_aux_p,
    inout  logic                                   dp_aux_n
);

    // DisplayPort Parameters
    localparam integer LANES = 4;
    localparam integer MAIN_LINK_RATE = 8100000000; // 8.1 Gbps per lane

    // 8b/10b Encoding
    localparam [9:0] K28_5 = 10'b1001111100;

    // Registers
    logic [9:0]                                     lane_data [0:3];
    logic [9:0]                                     encoded_data [0:3];
    logic                                           lane_clk [0:3];

    // Video Packet Structure
    logic [127:0]                                   video_packet;
    logic                                           packet_valid;

    // -------------------------------------------------------------------------
    // 8b/10b Encoder
    // -------------------------------------------------------------------------
    genvar i;
    generate
        for (i = 0; i < 4; i++) begin: lane_enc
            displayport_8b10b encoder (
                .pixel_clk      (pixel_clk),
                .rst_n          (rst_n),
                .data_in        ({pixel_data_r[11:4], pixel_data_g[11:4], pixel_data_b[11:4]}),
                .ctrl_in        ({pixel_de, pixel_hsync, pixel_vsync, 1'b0}),
                .encoded_out    (encoded_data[i])
            );
        end
    endgenerate

    // -------------------------------------------------------------------------
    // Lane Scrambler
    // -------------------------------------------------------------------------
    genvar j;
    generate
        for (j = 0; j < 4; j++) begin: lane_scram
            dp_scrambler scr (
                .pixel_clk      (pixel_clk),
                .rst_n          (rst_n),
                .data_in        (encoded_data[j]),
                .data_out       (lane_data[j])
            );
        end
    endgenerate

    // -------------------------------------------------------------------------
    // Serializer (10:1)
    // -------------------------------------------------------------------------
    genvar k;
    generate
        for (k = 0; k < 4; k++) begin: lane_ser
            dp_serializer #(
                .DATA_WIDTH     (10)
            ) ser (
                .pixel_clk      (pixel_clk),
                .rst_n          (rst_n),
                .data_in        (lane_data[k]),
                .ser_out_p      (dp_tx_data_p[k]),
                .ser_out_n      (dp_tx_data_n[k])
            );
        end
    endgenerate

    // -------------------------------------------------------------------------
    // Clock Channel
    // -------------------------------------------------------------------------
    dp_serializer #(
        .DATA_WIDTH     (1)
    ) clk_ser (
        .pixel_clk      (pixel_clk),
        .rst_n          (rst_n),
        .data_in        (1'b1),
        .ser_out_p      (dp_tx_clk_p),
        .ser_out_n      (dp_tx_clk_n)
    );

    // -------------------------------------------------------------------------
    // AUX Channel Controller
    // -------------------------------------------------------------------------
    dp_aux_controller aux_ctrl (
        .pixel_clk      (pixel_clk),
        .rst_n          (rst_n),
        .hpd            (dp_hpd),
        .aux_p          (dp_aux_p),
        .aux_n          (dp_aux_n)
    );

endmodule

// -----------------------------------------------------------------------------
// File: displayport_8b10b.sv
// Description: DisplayPort 8b/10b Encoder
// -----------------------------------------------------------------------------
module displayport_8b10b (
    input  logic                                    pixel_clk,
    input  logic                                    rst_n,
    input  logic [23:0]                             data_in,
    input  logic [3:0]                              ctrl_in,
    output logic [9:0]                              encoded_out
);

    logic [9:0]                                     encoded_data;

    // Simplified 8b/10b encoding
    always_ff @(posedge pixel_clk or negedge rst_n) begin
        if (!rst_n) begin
            encoded_out <= 10'd0;
        end else begin
            // Basic encoding - for actual implementation use full 8b/10b table
            encoded_out <= {1'b1, data_in[7:0], 1'b0};
        end
    end

endmodule

// -----------------------------------------------------------------------------
// File: dp_scrambler.sv
// Description: DisplayPort Lane Scrambler (PRBS-15)
// -----------------------------------------------------------------------------
module dp_scrambler (
    input  logic                                    pixel_clk,
    input  logic                                    rst_n,
    input  logic [9:0]                              data_in,
    output logic [9:0]                              data_out
);

    logic [14:0]                                    lfsr;

    always_ff @(posedge pixel_clk or negedge rst_n) begin
        if (!rst_n) begin
            lfsr <= 15'h7FFF;
            data_out <= '0;
        end else begin
            // PRBS-15 polynomial: x^15 + x^14 + 1
            lfsr <= {lfsr[13:0], lfsr[14] ^ lfsr[13]};
            data_out <= data_in ^ {lfsr[9:0], 5'd0};
        end
    end

endmodule

// -----------------------------------------------------------------------------
// File: dp_serializer.sv
// Description: DisplayPort Serializer - Parallel to Serial
// -----------------------------------------------------------------------------
module dp_serializer #(
    parameter integer DATA_WIDTH = 10
) (
    input  logic                                    pixel_clk,
    input  logic                                    rst_n,
    input  logic [DATA_WIDTH-1:0]                   data_in,
    output logic                                    ser_out_p,
    output logic                                    ser_out_n
);

    logic [DATA_WIDTH-1:0]                          shift_reg;
    integer                                         bit_count;

    always_ff @(posedge pixel_clk or negedge rst_n) begin
        if (!rst_n) begin
            shift_reg <= '0;
            bit_count <= 0;
        end else begin
            if (bit_count == 0) begin
                shift_reg <= data_in;
                bit_count <= DATA_WIDTH - 1;
            end else begin
                shift_reg <= {shift_reg[DATA_WIDTH-2:0], 1'b0};
                bit_count <= bit_count - 1;
            end
        end
    end

    assign ser_out_p = shift_reg[DATA_WIDTH-1];
    assign ser_out_n = ~shift_reg[DATA_WIDTH-1];

endmodule

// -----------------------------------------------------------------------------
// File: dp_aux_controller.sv
// Description: DisplayPort AUX Channel Controller
// -----------------------------------------------------------------------------
module dp_aux_controller (
    input  logic                                    pixel_clk,
    input  logic                                    rst_n,
    input  logic                                   hpd,
    inout  logic                                   aux_p,
    inout  logic                                   aux_n
);

    // AUX Channel is bidirectional LVDS
    tri1 aux_p;
    tri1 aux_n;

    // Simplified AUX implementation
    always_ff @(posedge pixel_clk or negedge rst_n) begin
        if (!rst_n) begin
            // Reset state
        end else begin
            if (hpd) begin
                // AUX communication enabled
            end
        end
    end

    assign aux_p = 1'bz;
    assign aux_n = 1'bz;

endmodule
