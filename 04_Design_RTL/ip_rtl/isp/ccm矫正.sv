// ============================================================
// Project: YaoGuang ISP
// Module:  ccm矫正.sv
// Description: Color Correction Matrix
// ============================================================

`timescale 1ns/1ps

module ccm矫正 #(
    parameter int DATA_WIDTH = 12,
    parameter int COEF_WIDTH = 12
) (
    input  logic                    clk_i,
    input  logic                    rst_n_i,
    input  logic                    cfg_enable_i,
    input  logic [11:0]             cfg_matrix_i[9],

    // RGB Input
    input  logic [23:0]             rgb_data_i,
    input  logic                    rgb_valid_i,

    // Corrected RGB Output
    output logic [23:0]             rgb_corrected_o,
    output logic                    rgb_valid_o
);

    // Fixed CCM coefficients for sRGB (standard color matrix)
    localparam [11:0] CCM_SRGB[9] = '{
        12'h1200,  // Rr = 1.125
        12'hFDA0,  // Rg = -0.03125
        12'h0220,  // Rb = 0.015625
        12'h0300,  // Gr = 0.015625
        12'h1200,  // Gg = 1.125
        12'hFDA0,  // Gb = -0.03125
        12'h0200,  // Br = 0.015625
        12'hFDA0,  // Bg = -0.03125
        12'h1200   // Bb = 1.125
    };

    // Current coefficients
    logic [11:0]                    ccm[9];

    // Pipeline registers
    logic [15:0]                    r_in, g_in, b_in;
    logic [27:0]                    r_mul[3];
    logic [27:0]                    g_mul[3];
    logic [27:0]                    b_mul[3];
    logic [19:0]                    r_sum, g_sum, b_sum;
    logic [23:0]                    rgb_clamped;

    // ============================================================
    // Coefficient Selection
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            ccm <= CCM_SRGB;
        end else begin
            if (cfg_enable_i) begin
                ccm <= cfg_matrix_i;
            end else begin
                ccm <= CCM_SRGB;
            end
        end
    end

    // ============================================================
    // Input Register
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            r_in <= '0;
            g_in <= '0;
            b_in <= '0;
        end else if (rgb_valid_i) begin
            r_in <= rgb_data_i[23:16];
            g_in <= rgb_data_i[15:8];
            b_in <= rgb_data_i[7:0];
        end
    end

    // ============================================================
    // Matrix Multiplication (3x3)
    // ============================================================
    always_ff @(posedge clk_i) begin
        // R = Rr*R + Rg*G + Rb*B
        r_mul[0] <= $signed(r_in) * $signed(ccm[0]);
        r_mul[1] <= $signed(g_in) * $signed(ccm[1]);
        r_mul[2] <= $signed(b_in) * $signed(ccm[2]);

        // G = Gr*R + Gg*G + Gb*B
        g_mul[0] <= $signed(r_in) * $signed(ccm[3]);
        g_mul[1] <= $signed(g_in) * $signed(ccm[4]);
        g_mul[2] <= $signed(b_in) * $signed(ccm[5]);

        // B = Br*R + Bg*G + Bb*B
        b_mul[0] <= $signed(r_in) * $signed(ccm[6]);
        b_mul[1] <= $signed(g_in) * $signed(ccm[7]);
        b_mul[2] <= $signed(b_in) * $signed(ccm[8]);
    end

    // ============================================================
    // Summation with rounding
    // ============================================================
    always_ff @(posedge clk_i) begin
        r_sum <= (r_mul[0] + r_mul[1] + r_mul[2]) >> 12;
        g_sum <= (g_mul[0] + g_mul[1] + g_mul[2]) >> 12;
        b_sum <= (b_mul[0] + b_mul[1] + b_mul[2]) >> 12;
    end

    // ============================================================
    // Clamping to valid range
    // ============================================================
    always_ff @(posedge clk_i) begin
        // Clamp R
        if (r_sum[19]) begin
            rgb_clamped[23:16] <= '0;
        end else if (r_sum[19:16] > 4'hF) begin
            rgb_clamped[23:16] <= 8'hFF;
        end else begin
            rgb_clamped[23:16] <= r_sum[15:8];
        end

        // Clamp G
        if (g_sum[19]) begin
            rgb_clamped[15:8] <= '0;
        end else if (g_sum[19:16] > 4'hF) begin
            rgb_clamped[15:8] <= 8'hFF;
        end else begin
            rgb_clamped[15:8] <= g_sum[15:8];
        end

        // Clamp B
        if (b_sum[19]) begin
            rgb_clamped[7:0] <= '0;
        end else if (b_sum[19:16] > 4'hF) begin
            rgb_clamped[7:0] <= 8'hFF;
        end else begin
            rgb_clamped[7:0] <= b_sum[15:8];
        end
    end

    // ============================================================
    // Output Register
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            rgb_corrected_o <= '0;
            rgb_valid_o <= '0;
        end else begin
            rgb_valid_o <= rgb_valid_i;
            rgb_corrected_o <= rgb_clamped;
        end
    end

endmodule
