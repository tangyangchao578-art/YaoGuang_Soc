// -----------------------------------------------------------------------------
// File: hdmi_tx.sv
// Description: HDMI 2.1 Transmitter - TMDS Encoder and PHY Interface
// Author: YaoGuang SoC Design Team
// Date: 2026-01-18
// -----------------------------------------------------------------------------

`timescale 1ns/1ps

module hdmi_tx #(
    parameter integer DATA_WIDTH = 12
) (
    input  logic                                    pixel_clk,
    input  logic                                    rst_n,
    input  logic                                    pixel_valid,
    input  logic [DATA_WIDTH-1:0]                   pixel_data_r,
    input  logic [DATA_WIDTH-1:0]                   pixel_data_g,
    input  logic [DATA_WIDTH-1:0]                   pixel_data_b,
    input  logic                                    pixel_de,
    input  logic                                    pixel_hsync,
    input  logic                                    pixel_vsync,

    output logic                                    hdmi_tx_clk_p,
    output logic                                    hdmi_tx_clk_n,
    output logic [2:0]                             hdmi_tx_data_p,
    output logic [2:0]                             hdmi_tx_data_n,
    input  logic                                   hdmi_hpd,
    output logic                                   hdmi_cec
);

    // TMDS Encoding Parameters
    localparam integer TMDS_Bits = 10;

    // HDMI Timing Parameters (1920x1080@60Hz)
    localparam integer PixelClock = 148500000; // 148.5 MHz

    // Registers
    logic [8:0]                                     tmds_ch0_d; // Blue channel
    logic [8:0]                                     tmds_ch1_d; // Green channel
    logic [8:0]                                     tmds_ch2_d; // Red channel
    logic                                           tmds_clk;

    logic [9:0]                                     enc_ch0;
    logic [9:0]                                     enc_ch1;
    logic [9:0]                                     enc_ch2;

    logic [DATA_WIDTH-1:0]                          data_r_sat;
    logic [DATA_WIDTH-1:0]                          data_g_sat;
    logic [DATA_WIDTH-1:0]                          data_b_sat;

    // Control Signals for TMDS
    logic [1:0]                                     c0, c1;
    logic                                           de;

    // -------------------------------------------------------------------------
    // Input Data Processing
    // -------------------------------------------------------------------------
    always_ff @(posedge pixel_clk or negedge rst_n) begin
        if (!rst_n) begin
            data_r_sat <= '0;
            data_g_sat <= '0;
            data_b_sat <= '0;
            c0 <= 2'd0;
            c1 <= 2'd0;
            de <= 1'b0;
        end else begin
            // Saturate to 8-bit for TMDS
            data_r_sat <= (pixel_data_r[DATA_WIDTH-1:4] == '1) ?
                          {8{1'b1}} : pixel_data_r[DATA_WIDTH-1:4];
            data_g_sat <= (pixel_data_g[DATA_WIDTH-1:4] == '1) ?
                          {8{1'b1}} : pixel_data_g[DATA_WIDTH-1:4];
            data_b_sat <= (pixel_data_b[DATA_WIDTH-1:4] == '1) ?
                          {8{1'b1}} : pixel_data_b[DATA_WIDTH-1:4];

            // Control signals
            c0 <= {pixel_hsync, pixel_vsync};
            c1 <= 2'd0;
            de <= pixel_de;
        end
    end

    // -------------------------------------------------------------------------
    // TMDS Encoder
    // -------------------------------------------------------------------------
    tmds_encoder #(
        .CHANNEL            (0)
    ) tmds_enc_ch0 (
        .pixel_clk          (pixel_clk),
        .rst_n              (rst_n),
        .data_in            (data_b_sat),
        .de                 (de),
        .c0                 (c0[0]),
        .c1                 (c1[0]),
        .tmds_out           (enc_ch0)
    );

    tmds_encoder #(
        .CHANNEL            (1)
    ) tmds_enc_ch1 (
        .pixel_clk          (pixel_clk),
        .rst_n              (rst_n),
        .data_in            (data_g_sat),
        .de                 (de),
        .c0                 (c0[1]),
        .c1                 (c1[1]),
        .tmds_out           (enc_ch1)
    );

    tmds_encoder #(
        .CHANNEL            (2)
    ) tmds_enc_ch2 (
        .pixel_clk          (pixel_clk),
        .rst_n              (rst_n),
        .data_in            (data_r_sat),
        .de                 (de),
        .c0                 (c0[0]),
        .c1                 (c1[0]),
        .tmds_out           (enc_ch2)
    );

    // -------------------------------------------------------------------------
    // TMDS Serializer (10:1)
    // -------------------------------------------------------------------------
    tmds_serializer #(
        .DATA_WIDTH         (10)
    ) serializer_ch0 (
        .pixel_clk          (pixel_clk),
        .rst_n              (rst_n),
        .data_in            (enc_ch0),
        .ser_out_p          (hdmi_tx_data_p[0]),
        .ser_out_n          (hdmi_tx_data_n[0])
    );

    tmds_serializer #(
        .DATA_WIDTH         (10)
    ) serializer_ch1 (
        .pixel_clk          (pixel_clk),
        .rst_n              (rst_n),
        .data_in            (enc_ch1),
        .ser_out_p          (hdmi_tx_data_p[1]),
        .ser_out_n          (hdmi_tx_data_n[1])
    );

    tmds_serializer #(
        .DATA_WIDTH         (10)
    ) serializer_ch2 (
        .pixel_clk          (pixel_clk),
        .rst_n              (rst_n),
        .data_in            (enc_ch2),
        .ser_out_p          (hdmi_tx_data_p[2]),
        .ser_out_n          (hdmi_tx_data_n[2])
    );

    // Clock Serializer (1:1)
    tmds_serializer #(
        .DATA_WIDTH         (1)
    ) serializer_clk (
        .pixel_clk          (pixel_clk),
        .rst_n              (rst_n),
        .data_in            (1'b1),
        .ser_out_p          (hdmi_tx_clk_p),
        .ser_out_n          (hdmi_tx_clk_n)
    );

    // -------------------------------------------------------------------------
    // CEC and HPD Management
    // -------------------------------------------------------------------------
    always_ff @(posedge pixel_clk or negedge rst_n) begin
        if (!rst_n) begin
            hdmi_cec <= 1'bZ;
        end else begin
            // CEC is open-drain, pull-up required externally
            hdmi_cec <= 1'bZ;
        end
    end

endmodule

// -----------------------------------------------------------------------------
// File: tmds_encoder.sv
// Description: TMDS Encoder for HDMI
// -----------------------------------------------------------------------------
module tmds_encoder #(
    parameter integer CHANNEL = 0
) (
    input  logic                                    pixel_clk,
    input  logic                                    rst_n,
    input  logic [7:0]                              data_in,
    input  logic                                    de,
    input  logic                                    c0,
    input  logic                                    c1,
    output logic [9:0]                              tmds_out
);

    logic [8:0]                                     q_out;
    logic                                           ctrl;

    always_comb begin
        if (!de) begin
            case ({c0, c1})
                2'b00:   q_out = 9'b110101010;
                2'b01:   q_out = 9'b001010101;
                2'b10:   q_out = 9'b010101010;
                default: q_out = 9'b101010101;
            endcase
        end else begin
            // Data island encoding
            ctrl = 1'b0;
            q_out = {1'b1, data_in};
        end
    end

    assign tmds_out = {q_out, ctrl};

endmodule

// -----------------------------------------------------------------------------
// File: tmds_serializer.sv
// Description: TMDS Serializer - Parallel to Serial Converter
// -----------------------------------------------------------------------------
module tmds_serializer #(
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

    // LVDS Output Driver
    assign ser_out_p = shift_reg[DATA_WIDTH-1];
    assign ser_out_n = ~shift_reg[DATA_WIDTH-1];

endmodule
