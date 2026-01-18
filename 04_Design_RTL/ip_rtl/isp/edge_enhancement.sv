// ============================================================
// Project: YaoGuang ISP
// Module:  edge_enhancement.sv
// Description: Edge Enhancement / Sharpening
// ============================================================

`timescale 1ns/1ps

module edge_enhancement #(
    parameter int DATA_WIDTH = 12
) (
    input  logic                    clk_i,
    input  logic                    rst_n_i,
    input  logic                    cfg_enable_i,
    input  logic [7:0]              cfg_strength_i,

    // RGB Input
    input  logic [23:0]             rgb_data_i,
    input  logic                    rgb_valid_i,

    // Sharpened Output
    output logic [23:0]             rgb_sharpened_o,
    output logic                    rgb_valid_o
);

    // Line buffer configuration
    localparam int BUFFER_WIDTH = 4096;

    // Line buffers for edge detection
    logic [23:0]                    line_buffer[3][BUFFER_WIDTH];
    logic [1:0]                     line_idx;
    logic [12:0]                    pixel_idx;

    // Laplacian kernel coefficients
    localparam [7:0] LAPLACIAN[3][3] = '{
        '{8'h00, 8'h01, 8'h00},
        '{8'h01, 8'hFC, 8'h01},
        '{8'h00, 8'h01, 8'h00}
    };

    // Original and enhanced values
    logic [7:0]                     r_orig, g_orig, b_orig;
    logic [7:0]                     r_edge, g_edge, b_edge;
    logic [7:0]                     r_sharp, g_sharp, b_sharp;
    logic [23:0]                    rgb_sharpened_reg;

    // Threshold for edge detection
    logic [7:0]                     edge_threshold;

    // ============================================================
    // Line Buffer Management
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            line_idx <= '0;
            pixel_idx <= '0;
        end else if (rgb_valid_i) begin
            line_buffer[line_idx][pixel_idx] <= rgb_data_i;
            pixel_idx <= pixel_idx + 1;
            if (pixel_idx == BUFFER_WIDTH - 1) begin
                pixel_idx <= '0;
                line_idx <= line_idx + 1;
            end
        end
    end

    // ============================================================
    // Edge Detection (Laplacian)
    // ============================================================
    always_comb begin
        if (!cfg_enable_i) begin
            r_edge = '0;
            g_edge = '0;
            b_edge = '0;
        end else begin
            // Calculate Laplacian for each channel
            r_edge = 0;
            g_edge = 0;
            b_edge = 0;

            for (int i = 0; i < 3; i++) begin
                for (int j = 0; j < 3; j++) begin
                    logic [23:0] neighbor;
                    neighbor = line_buffer[(line_idx + i) % 3][pixel_idx + j - 1];

                    r_edge = r_edge + (neighbor[23:16] * LAPLACIAN[i][j]);
                    g_edge = g_edge + (neighbor[15:8] * LAPLACIAN[i][j]);
                    b_edge = b_edge + (neighbor[7:0] * LAPLACIAN[i][j]);
                end
            end
        end
    end

    // ============================================================
    // Original Pixel Value
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            r_orig <= '0;
            g_orig <= '0;
            b_orig <= '0;
        end else if (rgb_valid_i) begin
            r_orig <= rgb_data_i[23:16];
            g_orig <= rgb_data_i[15:8];
            b_orig <= rgb_data_i[7:0];
        end
    end

    // ============================================================
    // Unsharp Masking
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            r_sharp <= '0;
            g_sharp <= '0;
            b_sharp <= '0;
        end else begin
            if (cfg_enable_i) begin
                edge_threshold = cfg_strength_i;

                // Apply unsharp mask: sharpened = original + strength * edge
                // R channel
                if (r_edge > edge_threshold) begin
                    r_sharp = r_orig + ((r_edge * cfg_strength_i) >> 4);
                end else if (r_edge < -edge_threshold) begin
                    r_sharp = r_orig - ((-r_edge * cfg_strength_i) >> 4);
                end else begin
                    r_sharp = r_orig;
                end

                // G channel
                if (g_edge > edge_threshold) begin
                    g_sharp = g_orig + ((g_edge * cfg_strength_i) >> 4);
                end else if (g_edge < -edge_threshold) begin
                    g_sharp = g_orig - ((-g_edge * cfg_strength_i) >> 4);
                end else begin
                    g_sharp = g_orig;
                end

                // B channel
                if (b_edge > edge_threshold) begin
                    b_sharp = b_orig + ((b_edge * cfg_strength_i) >> 4);
                end else if (b_edge < -edge_threshold) begin
                    b_sharp = b_orig - ((-b_edge * cfg_strength_i) >> 4);
                end else begin
                    b_sharp = b_orig;
                end

                // Clamp to valid range
                if (r_sharp > 8'hFF) r_sharp = 8'hFF;
                if (r_sharp < 8'h00) r_sharp = 8'h00;
                if (g_sharp > 8'hFF) g_sharp = 8'hFF;
                if (g_sharp < 8'h00) g_sharp = 8'h00;
                if (b_sharp > 8'hFF) b_sharp = 8'hFF;
                if (b_sharp < 8'h00) b_sharp = 8'h00;

                rgb_sharpened_reg <= {r_sharp, g_sharp, b_sharp};
            end else begin
                rgb_sharpened_reg <= rgb_data_i;
            end
        end
    end

    // ============================================================
    // Output Register
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            rgb_sharpened_o <= '0;
            rgb_valid_o <= '0;
        end else begin
            rgb_valid_o <= rgb_valid_i;
            rgb_sharpened_o <= rgb_sharpened_reg;
        end
    end

endmodule
