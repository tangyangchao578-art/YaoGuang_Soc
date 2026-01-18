// ============================================================
// Project: YaoGuang ISP
// Module:  gamma_correction.sv
// Description: Gamma Encoding with LUT
// ============================================================

`timescale 1ns/1ps

module gamma_correction #(
    parameter int LUT_SIZE = 256,
    parameter int DATA_WIDTH = 12
) (
    input  logic                    clk_i,
    input  logic                    rst_n_i,
    input  logic                    cfg_enable_i,
    input  logic [11:0]             cfg_lut_i[256],

    // RGB Input
    input  logic [23:0]             rgb_data_i,
    input  logic                    rgb_valid_i,

    // Gamma Corrected Output
    output logic [23:0]             rgb_gamma_o,
    output logic                    rgb_valid_o
);

    // Default Gamma 2.2 LUT
    function automatic [11:0] gamma2_2_lut(input int index);
        real value;
        value = (index / 255.0) ** (1.0 / 2.2);
        gamma2_2_lut = $rtoi(value * 4095);
    endfunction

    // Gamma LUT initialization
    logic [11:0]                    gamma_lut[256];

    // Input pipeline
    logic [7:0]                     r_in_idx, g_in_idx, b_in_idx;
    logic [23:0]                    rgb_reg;

    // Output pipeline
    logic [11:0]                    r_gamma, g_gamma, b_gamma;
    logic [23:0]                    rgb_gamma_reg;

    // ============================================================
    // Gamma LUT Initialization
    // ============================================================
    initial begin
        for (int i = 0; i < 256; i++) begin
            gamma_lut[i] = gamma2_2_lut(i);
        end
    end

    // ============================================================
    // LUT Update from Configuration
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            // LUT will be initialized with gamma 2.2
        end else begin
            if (cfg_enable_i) begin
                gamma_lut <= cfg_lut_i;
            end
        end
    end

    // ============================================================
    // Input Stage
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            r_in_idx <= '0;
            g_in_idx <= '0;
            b_in_idx <= '0;
            rgb_reg <= '0;
        end else if (rgb_valid_i) begin
            // Map 12-bit input to 8-bit LUT index
            r_in_idx <= rgb_data_i[23:16] >> 4;
            g_in_idx <= rgb_data_i[15:8] >> 4;
            b_in_idx <= rgb_data_i[7:0] >> 4;
            rgb_reg <= rgb_data_i;
        end
    end

    // ============================================================
    // LUT Lookup Pipeline
    // ============================================================
    always_ff @(posedge clk_i) begin
        if (cfg_enable_i) begin
            r_gamma <= gamma_lut[r_in_idx];
            g_gamma <= gamma_lut[g_in_idx];
            b_gamma <= gamma_lut[b_in_idx];
        end else begin
            r_gamma <= gamma_lut[r_in_idx];
            g_gamma <= gamma_lut[g_in_idx];
            b_gamma <= gamma_lut[b_in_idx];
        end
    end

    // ============================================================
    // Output Stage
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            rgb_gamma_o <= '0;
            rgb_valid_o <= '0;
        end else begin
            rgb_valid_o <= rgb_valid_i;
            rgb_gamma_o <= {r_gamma[11:4], g_gamma[11:4], b_gamma[11:4]};
        end
    end

endmodule
