// ============================================================
// Project: YaoGuang ISP
// Module:  noise_reduction.sv
// Description: 2D/3D Noise Reduction
// ============================================================

`timescale 1ns/1ps

module noise_reduction #(
    parameter int DATA_WIDTH = 12
) (
    input  logic                    clk_i,
    input  logic                    rst_n_i,
    input  logic                    cfg_enable_i,
    input  logic [7:0]              cfg_strength_i,

    // RGB Input
    input  logic [23:0]             rgb_data_i,
    input  logic                    rgb_valid_i,

    // Denoised Output
    output logic [23:0]             rgb_denoised_o,
    output logic                    rgb_valid_o
);

    // Buffer configuration
    localparam int BUFFER_WIDTH = 4096;
    localparam int NR_WINDOW = 3;

    // Frame buffers for 3D NR
    logic [23:0]                    frame_buffer[3][BUFFER_WIDTH];
    logic [1:0]                     frame_idx;
    logic [12:0]                    pixel_idx;
    logic                           frame_start;

    // Current frame line buffer
    logic [23:0]                    line_buffer[3][BUFFER_WIDTH];
    logic [1:0]                     line_idx;

    // 3x3 window for 2D NR
    logic [23:0]                    window[3][3];

    // Temporal average buffer
    logic [23:0]                    temporal_avg;
    logic                           temporal_valid;

    // Processed values
    logic [23:0]                    spatial_filtered;
    logic [23:0]                    temporal_filtered;
    logic [23:0]                    final_filtered;

    // Motion detection
    logic [15:0]                    motion_threshold;
    logic [15:0]                    motion_score;

    // ============================================================
    // Frame Buffer Management (3D NR)
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            frame_idx <= '0;
            pixel_idx <= '0;
        end else if (rgb_valid_i) begin
            // Store current pixel in frame buffer
            frame_buffer[frame_idx][pixel_idx] <= rgb_data_i;

            pixel_idx <= pixel_idx + 1;
            if (pixel_idx == BUFFER_WIDTH - 1) begin
                pixel_idx <= '0;
                frame_idx <= frame_idx + 1;
            end
        end
    end

    // ============================================================
    // Line Buffer for Spatial Filtering
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            line_idx <= '0;
        end else if (rgb_valid_i) begin
            line_buffer[line_idx][pixel_idx] <= rgb_data_i;
            line_idx <= line_idx + 1;
        end
    end

    // ============================================================
    // 3x3 Window Extraction
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            for (int i = 0; i < 3; i++) begin
                for (int j = 0; j < 3; j++) begin
                    window[i][j] <= '0;
                end
            end
        end else if (rgb_valid_i) begin
            // Extract 3x3 window from line buffer
            for (int i = 0; i < 3; i++) begin
                for (int j = 0; j < 3; j++) begin
                    if (i == 1 && j == 1) begin
                        window[i][j] <= rgb_data_i;
                    end else begin
                        window[i][j] <= line_buffer[(line_idx + i) % 3][pixel_idx + j - 1];
                    end
                end
            end
        end
    end

    // ============================================================
    // 2D Spatial Filter (Bilateral-like)
    // ============================================================
    always_comb begin
        if (!cfg_enable_i) begin
            spatial_filtered = rgb_data_i;
        end else begin
            // Simple box filter with edge preservation
            logic [31:0] r_sum, g_sum, b_sum;
            logic [31:0] r_weighted, g_weighted, b_weighted;
            logic [15:0] center_r, center_g, center_b;
            logic [15:0] weight_total;
            logic [15:0] weight;

            center_r = rgb_data_i[23:16];
            center_g = rgb_data_i[15:8];
            center_b = rgb_data_i[7:0];

            r_sum = '0;
            g_sum = '0;
            b_sum = '0;
            weight_total = '0;

            for (int i = 0; i < 3; i++) begin
                for (int j = 0; j < 3; j++) begin
                    // Calculate weight based on intensity difference
                    logic [15:0] diff_r, diff_g, diff_b;
                    logic [15:0] pixel_r, pixel_g, pixel_b;
                    logic [15:0] abs_diff;

                    pixel_r = window[i][j][23:16];
                    pixel_g = window[i][j][15:8];
                    pixel_b = window[i][j][7:0];

                    diff_r = (pixel_r > center_r) ? (pixel_r - center_r) : (center_r - pixel_r);
                    diff_g = (pixel_g > center_g) ? (pixel_g - center_g) : (center_g - pixel_g);
                    diff_b = (pixel_b > center_b) ? (pixel_b - center_b) : (center_b - pixel_b);

                    abs_diff = (diff_r + diff_g + diff_b) / 3;

                    // Weight decreases with intensity difference
                    weight = 256 - (abs_diff >> cfg_strength_i);

                    r_sum = r_sum + (pixel_r * weight);
                    g_sum = g_sum + (pixel_g * weight);
                    b_sum = b_sum + (pixel_b * weight);
                    weight_total = weight_total + weight;
                end
            end

            if (weight_total > 0) begin
                spatial_filtered[23:16] = r_sum / weight_total;
                spatial_filtered[15:8] = g_sum / weight_total;
                spatial_filtered[7:0] = b_sum / weight_total;
            end else begin
                spatial_filtered = rgb_data_i;
            end
        end
    end

    // ============================================================
    // Temporal Filtering (Frame Averaging)
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            temporal_avg <= '0;
            temporal_valid <= '0;
        end else if (rgb_valid_i) begin
            temporal_valid <= '1;

            if (frame_idx > 0) begin
                // Average with previous frame
                temporal_avg <= (rgb_data_i + frame_buffer[frame_idx-1][pixel_idx]) >> 1;
            end else begin
                temporal_avg <= rgb_data_i;
            end
        end
    end

    // ============================================================
    // Motion-Adaptive Blending
    // ============================================================
    always_comb begin
        if (!cfg_enable_i) begin
            final_filtered = rgb_data_i;
        end else begin
            // Calculate motion score
            logic [15:0] diff_r, diff_g, diff_b;

            diff_r = (spatial_filtered[23:16] > temporal_avg[23:16]) ?
                     (spatial_filtered[23:16] - temporal_avg[23:16]) :
                     (temporal_avg[23:16] - spatial_filtered[23:16]);
            diff_g = (spatial_filtered[15:8] > temporal_avg[15:8]) ?
                     (spatial_filtered[15:8] - temporal_avg[15:8]) :
                     (temporal_avg[15:8] - spatial_filtered[15:8]);
            diff_b = (spatial_filtered[7:0] > temporal_avg[7:0]) ?
                     (spatial_filtered[7:0] - temporal_avg[7:0]) :
                     (temporal_avg[7:0] - spatial_filtered[7:0]);

            motion_score = diff_r + diff_g + diff_b;
            motion_threshold = cfg_strength_i * 64;

            if (motion_score > motion_threshold) begin
                // High motion - use spatial filter
                final_filtered = spatial_filtered;
            end else begin
                // Low motion - blend spatial and temporal
                final_filtered = (spatial_filtered + temporal_avg) >> 1;
            end
        end
    end

    // ============================================================
    // Output Register
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            rgb_denoised_o <= '0;
            rgb_valid_o <= '0;
        end else begin
            rgb_valid_o <= rgb_valid_i;
            rgb_denoised_o <= final_filtered;
        end
    end

endmodule
