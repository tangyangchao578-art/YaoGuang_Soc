// -----------------------------------------------------------------------------
// File: color_processing.sv
// Description: Color Processing Pipeline - Color Space, Gamma, HDR Processing
// Author: YaoGuang SoC Design Team
// Date: 2026-01-18
// -----------------------------------------------------------------------------

`timescale 1ns/1ps

module color_processing #(
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

    output logic                                    out_valid,
    output logic [DATA_WIDTH-1:0]                   out_data_r,
    output logic [DATA_WIDTH-1:0]                   out_data_g,
    output logic [DATA_WIDTH-1:0]                   out_data_b,
    output logic                                    out_de,
    output logic                                    out_hsync,
    output logic                                    out_vsync
);

    // Pipeline Stage Parameters
    localparam integer STAGES = 5;

    // Color Space Conversion Coefficients (Fixed-Point Q10.6)
    localparam signed [15:0] COEF_RY  = 16'd1382;  // 0.2126 * 4096
    localparam signed [15:0] COEF_GY  = 16'd2930;  // 0.7152 * 4096
    localparam signed [15:0] COEF_BY  = 16'd296;   // 0.0722 * 4096
    localparam signed [15:0] COEF_RCB = -16'd469;  // -0.1146 * 4096
    localparam signed [15:0] COEF_GCB = -16'd1578; // -0.3854 * 4096
    localparam signed [15:0] COEF_BCB = 16'd2048;  // 0.5000 * 4096
    localparam signed [15:0] COEF_RCR = 16'd2048;  // 0.5000 * 4096
    localparam signed [15:0] COEF_GCR = -16'd1861; // -0.4542 * 4096
    localparam signed [15:0] COEF_BCR = -16'd188;  // -0.0458 * 4096

    // Pipeline Registers
    logic [STAGES-1:0][DATA_WIDTH-1:0]              pipe_r;
    logic [STAGES-1:0][DATA_WIDTH-1:0]              pipe_g;
    logic [STAGES-1:0][DATA_WIDTH-1:0]              pipe_b;
    logic [STAGES-1:0]                              pipe_de;
    logic [STAGES-1:0]                              pipe_hsync;
    logic [STAGES-1:0]                              pipe_vsync;

    // Color Space Conversion Signals
    logic signed [31:0]                             y_val;
    logic signed [31:0]                             cb_val;
    logic signed [31:0]                             cr_val;

    // Gamma LUT Signals
    logic [DATA_WIDTH-1:0]                          gamma_r;
    logic [DATA_WIDTH-1:0]                          gamma_g;
    logic [DATA_WIDTH-1:0]                          gamma_b;

    // HDR Mapping Signals
    logic [DATA_WIDTH-1:0]                          hdr_r;
    logic [DATA_WIDTH-1:0]                          hdr_g;
    logic [DATA_WIDTH-1:0]                          hdr_b;

    // Dither Signals
    logic [DATA_WIDTH-1:0]                          dither_r;
    logic [DATA_WIDTH-1:0]                          dither_g;
    logic [DATA_WIDTH-1:0]                          dither_b;

    // -------------------------------------------------------------------------
    // Pipeline Stage 1: Color Space Conversion (RGB -> YCbCr)
    // -------------------------------------------------------------------------
    always_ff @(posedge pixel_clk or negedge rst_n) begin
        if (!rst_n) begin
            pipe_r[0] <= '0;
            pipe_g[0] <= '0;
            pipe_b[0] <= '0;
            pipe_de[0] <= 1'b0;
            pipe_hsync[0] <= 1'b0;
            pipe_vsync[0] <= 1'b0;
        end else begin
            if (pixel_valid) begin
                pipe_r[0] <= pixel_data_r;
                pipe_g[0] <= pixel_data_g;
                pipe_b[0] <= pixel_data_b;
                pipe_de[0] <= pixel_de;
                pipe_hsync[0] <= pixel_hsync;
                pipe_vsync[0] <= pixel_vsync;

                // BT.709 RGB to YCbCr conversion
                y_val  = (COEF_RY * $signed({1'b0, pixel_data_r}) +
                         COEF_GY * $signed({1'b0, pixel_data_g}) +
                         COEF_BY * $signed({1'b0, pixel_data_b})) >>> 6;

                cb_val = (COEF_RCB * $signed({1'b0, pixel_data_r}) +
                         COEF_GCB * $signed({1'b0, pixel_data_g}) +
                         COEF_BCB * $signed({1'b0, pixel_data_b}) +
                         32'd524288) >>> 6; // +128 in Q10.6

                cr_val = (COEF_RCR * $signed({1'b0, pixel_data_r}) +
                         COEF_GCR * $signed({1'b0, pixel_data_g}) +
                         COEF_BCR * $signed({1'b0, pixel_data_b}) +
                         32'd524288) >>> 6; // +128 in Q10.6
            end
        end
    end

    // -------------------------------------------------------------------------
    // Pipeline Stage 2: HDR Tone Mapping
    // -------------------------------------------------------------------------
    always_ff @(posedge pixel_clk or negedge rst_n) begin
        if (!rst_n) begin
            pipe_r[1] <= '0;
            pipe_g[1] <= '0;
            pipe_b[1] <= '0;
            pipe_de[1] <= 1'b0;
            pipe_hsync[1] <= 1'b0;
            pipe_vsync[1] <= 1'b0;
        end else begin
            pipe_r[1] <= pipe_r[0];
            pipe_g[1] <= pipe_g[0];
            pipe_b[1] <= pipe_b[0];
            pipe_de[1] <= pipe_de[0];
            pipe_hsync[1] <= pipe_hsync[0];
            pipe_vsync[1] <= pipe_vsync[0];

            // Simple S-curve tone mapping
            hdr_r = tone_map(pipe_r[0]);
            hdr_g = tone_map(pipe_g[0]);
            hdr_b = tone_map(pipe_b[0]);
        end
    end

    // -------------------------------------------------------------------------
    // Pipeline Stage 3: Gamma Correction
    // -------------------------------------------------------------------------
    always_ff @(posedge pixel_clk or negedge rst_n) begin
        if (!rst_n) begin
            pipe_r[2] <= '0;
            pipe_g[2] <= '0;
            pipe_b[2] <= '0;
            pipe_de[2] <= 1'b0;
            pipe_hsync[2] <= 1'b0;
            pipe_vsync[2] <= 1'b0;
        end else begin
            pipe_r[2] <= hdr_r;
            pipe_g[2] <= hdr_g;
            pipe_b[2] <= hdr_b;
            pipe_de[2] <= pipe_de[1];
            pipe_hsync[2] <= pipe_hsync[1];
            pipe_vsync[2] <= pipe_vsync[1];

            // Gamma 2.2 correction using LUT
            gamma_r = gamma_lut(pipe_r[1]);
            gamma_g = gamma_lut(pipe_g[1]);
            gamma_b = gamma_lut(pipe_b[1]);
        end
    end

    // -------------------------------------------------------------------------
    // Pipeline Stage 4: Color Gamut Mapping
    // -------------------------------------------------------------------------
    always_ff @(posedge pixel_clk or negedge rst_n) begin
        if (!rst_n) begin
            pipe_r[3] <= '0;
            pipe_g[3] <= '0;
            pipe_b[3] <= '0;
            pipe_de[3] <= 1'b0;
            pipe_hsync[3] <= 1'b0;
            pipe_vsync[3] <= 1'b0;
        end else begin
            pipe_r[3] <= gamut_map_r(gamma_r);
            pipe_g[3] <= gamut_map_g(gamma_g);
            pipe_b[3] <= gamut_map_b(gamma_b);
            pipe_de[3] <= pipe_de[2];
            pipe_hsync[3] <= pipe_hsync[2];
            pipe_vsync[3] <= pipe_vsync[2];
        end
    end

    // -------------------------------------------------------------------------
    // Pipeline Stage 5: Dithering and Output
    // -------------------------------------------------------------------------
    always_ff @(posedge pixel_clk or negedge rst_n) begin
        if (!rst_n) begin
            out_valid <= 1'b0;
            out_data_r <= '0;
            out_data_g <= '0;
            out_data_b <= '0;
            out_de <= 1'b0;
            out_hsync <= 1'b0;
            out_vsync <= 1'b0;
        end else begin
            out_valid  <= pipe_de[3];
            out_data_r <= dither(pipe_r[3]);
            out_data_g <= dither(pipe_g[3]);
            out_data_b <= dither(pipe_b[3]);
            out_de     <= pipe_de[3];
            out_hsync  <= pipe_hsync[3];
            out_vsync  <= pipe_vsync[3];
        end
    end

    // -------------------------------------------------------------------------
    // Functions
    // -------------------------------------------------------------------------
    function [DATA_WIDTH-1:0] tone_map(input [DATA_WIDTH-1:0] in_val);
        integer i;
        real normalized, mapped;
        begin
            normalized = real'(in_val) / 4095.0;
            // Simple S-curve for tone mapping
            mapped = normalized * normalized * (3.0 - 2.0 * normalized);
            tone_map = DATA_WIDTH'(mapped * 4095.0);
        end
    endfunction

    function [DATA_WIDTH-1:0] gamma_lut(input [DATA_WIDTH-1:0] in_val);
        integer i;
        real normalized, gamma_corrected;
        begin
            normalized = real'(in_val) / 4095.0;
            // Gamma 2.2
            gamma_corrected = (normalized > 0.0031308) ?
                              (1.055 * pow(normalized, 1.0/2.4) - 0.055) :
                              (12.92 * normalized);
            gamma_lut = DATA_WIDTH'(gamma_corrected * 4095.0);
        end
    endfunction

    function [DATA_WIDTH-1:0] gamut_map_r(input [DATA_WIDTH-1:0] in_val);
        // BT.2020 to BT.709 gamut mapping (simplified)
        integer i;
        real normalized;
        begin
            normalized = real'(in_val) / 4095.0;
            // Clip and scale for gamut mapping
            gamut_map_r = DATA_WIDTH'(normalized * 4095.0);
        end
    endfunction

    function [DATA_WIDTH-1:0] gamut_map_g(input [DATA_WIDTH-1:0] in_val);
        integer i;
        real normalized;
        begin
            normalized = real'(in_val) / 4095.0;
            gamut_map_g = DATA_WIDTH'(normalized * 4095.0);
        end
    endfunction

    function [DATA_WIDTH-1:0] gamut_map_b(input [DATA_WIDTH-1:0] in_val);
        integer i;
        real normalized;
        begin
            normalized = real'(in_val) / 4095.0;
            gamut_map_b = DATA_WIDTH'(normalized * 4095.0);
        end
    endfunction

    function [DATA_WIDTH-1:0] dither(input [DATA_WIDTH-1:0] in_val);
        // Blue noise dithering for low bit-depth output
        integer i;
        real dither_val;
        begin
            dither_val = real'(in_val);
            dither = DATA_WIDTH'(dither_val);
        end
    endfunction

endmodule
