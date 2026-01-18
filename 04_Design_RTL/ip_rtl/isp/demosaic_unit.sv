// ============================================================
// Project: YaoGuang ISP
// Module:  demosaic_unit.sv
// Description: Demosaic - Bayer to RGB Conversion
// ============================================================

`timescale 1ns/1ps

module demosaic_unit #(
    parameter int DATA_WIDTH = 16
) (
    input  logic                    clk_i,
    input  logic                    rst_n_i,
    input  logic                    cfg_enable_i,

    // Bayer Input
    input  logic [23:0]             bayer_data_i,
    input  logic                    bayer_valid_i,

    // RGB Output
    output logic [23:0]             rgb_data_o,
    output logic                    rgb_valid_o
);

    // Line buffers for 3x3 kernel
    localparam int BUFFER_WIDTH = 4096;
    logic [7:0]                     line_buffer[3][BUFFER_WIDTH];
    logic [2:0]                     row_idx;
    logic [12:0]                    col_idx;
    logic                           frame_start;

    // Bayer pattern detection
    logic [7:0]                     p00, p01, p02;
    logic [7:0]                     p10, p11, p12;
    logic [7:0]                     p20, p21, p22;

    logic [1:0]                     bayer_pattern;
    logic [15:0]                    g_h, g_v, g_d1, g_d2;
    logic [15:0]                    r_diff, b_diff;

    // Interpolated values
    logic [7:0]                     r_out, g_out, b_out;
    logic [7:0]                     r_interp, g_interp, b_interp;

    // ============================================================
    // Line Buffer Management
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            row_idx <= '0;
            col_idx <= '0;
        end else if (bayer_valid_i) begin
            // Update line buffers
            line_buffer[row_idx][col_idx] <= bayer_data_i[7:0];

            if (col_idx == BUFFER_WIDTH - 1) begin
                col_idx <= '0;
                row_idx <= (row_idx == 2) ? 0 : row_idx + 1;
            end else begin
                col_idx <= col_idx + 1;
            end
        end
    end

    // ============================================================
    // 3x3 Window Extraction
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            p00 <= '0; p01 <= '0; p02 <= '0;
            p10 <= '0; p11 <= '0; p12 <= '0;
            p20 <= '0; p21 <= '0; p22 <= '0;
            bayer_pattern <= '0;
        end else begin
            // Read 3x3 window from buffers
            p00 <= line_buffer[(row_idx == 0) ? 2 : row_idx-1][col_idx > 0 ? col_idx-1 : 0];
            p01 <= line_buffer[(row_idx == 0) ? 2 : row_idx-1][col_idx];
            p02 <= line_buffer[(row_idx == 0) ? 2 : row_idx-1][col_idx < BUFFER_WIDTH-1 ? col_idx+1 : BUFFER_WIDTH-1];

            p10 <= line_buffer[row_idx][col_idx > 0 ? col_idx-1 : 0];
            p11 <= line_buffer[row_idx][col_idx];
            p12 <= line_buffer[row_idx][col_idx < BUFFER_WIDTH-1 ? col_idx+1 : BUFFER_WIDTH-1];

            p20 <= line_buffer[(row_idx == 2) ? 0 : row_idx+1][col_idx > 0 ? col_idx-1 : 0];
            p21 <= line_buffer[(row_idx == 2) ? 0 : row_idx+1][col_idx];
            p22 <= line_buffer[(row_idx == 2) ? 0 : row_idx+1][col_idx < BUFFER_WIDTH-1 ? col_idx+1 : BUFFER_WIDTH-1];

            // Determine Bayer pattern (RG, BG, GR, GB)
            bayer_pattern[0] = col_idx[0];
            bayer_pattern[1] = row_idx[0];
        end
    end

    // ============================================================
    // Advanced Adaptive Demosaic Algorithm
    // ============================================================
    always_comb begin
        if (!cfg_enable_i) begin
            // Bypass mode - just replicate center pixel
            r_out = p11;
            g_out = p11;
            b_out = p11;
        end else begin
            // Determine center pixel color
            case (bayer_pattern)
                2'b00: begin // Red pixel at center
                    r_out = p11;

                    // Horizontal G interpolation
                    g_h = (p10 + p12);

                    // Vertical G interpolation
                    g_v = (p01 + p21);

                    // Diagonal G interpolation
                    g_d1 = (p00 + p22);
                    g_d2 = (p02 + p20);

                    // Adaptive G selection based on gradients
                    if ($abs(p01 - p21) < $abs(p10 - p12)) begin
                        g_out = (g_v >> 1);
                    end else begin
                        g_out = (g_h >> 1);
                    end

                    // B interpolation at red positions
                    b_interp = (p00 + p02 + p20 + p22) >> 2;
                    b_out = b_interp;
                end

                2'b01: begin // Green pixel at center (top-left is Red)
                    g_out = p11;

                    // R interpolation from horizontal neighbors
                    r_h = (p10);

                    // R interpolation from vertical neighbors
                    r_v = (p01);

                    // R interpolation from diagonals
                    r_d1 = (p00);
                    r_d2 = (p22);

                    // Adaptive R selection
                    if ($abs(p01 - p10) < $abs(p00 - p22)) begin
                        r_out = (r_h + r_v) >> 1;
                    end else begin
                        r_out = (r_d1 + r_d2) >> 1;
                    end

                    // B interpolation
                    b_interp = (p12 + p21);
                    b_out = b_interp >> 1;
                end

                2'b10: begin // Green pixel at center (top-left is Blue)
                    g_out = p11;

                    // B interpolation
                    b_h = (p10);
                    b_v = (p01);
                    b_d1 = (p22);
                    b_d2 = (p02);

                    if ($abs(p01 - p10) < $abs(p02 - p22)) begin
                        b_out = (b_h + b_v) >> 1;
                    end else begin
                        b_out = (b_d1 + b_d2) >> 1;
                    end

                    // R interpolation
                    r_interp = (p12 + p21);
                    r_out = r_interp >> 1;
                end

                2'b11: begin // Blue pixel at center
                    b_out = p11;

                    // G interpolation
                    g_h = (p10 + p12);
                    g_v = (p01 + p21);
                    g_d1 = (p00 + p22);
                    g_d2 = (p02 + p20);

                    if ($abs(p01 - p21) < $abs(p10 - p12)) begin
                        g_out = (g_v >> 1);
                    end else begin
                        g_out = (g_h >> 1);
                    end

                    // R interpolation
                    r_interp = (p00 + p02 + p20 + p22) >> 2;
                    r_out = r_interp;
                end
            endcase
        end
    end

    // ============================================================
    // Output Register
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            rgb_data_o <= '0;
            rgb_valid_o <= '0;
        end else begin
            rgb_valid_o <= bayer_valid_i;
            if (bayer_valid_i) begin
                rgb_data_o <= {r_out, g_out, b_out};
            end
        end
    end

endmodule
