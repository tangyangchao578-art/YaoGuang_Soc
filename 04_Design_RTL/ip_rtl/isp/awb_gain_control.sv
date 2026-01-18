// ============================================================
// Project: YaoGuang ISP
// Module:  awb_gain_control.sv
// Description: Automatic White Balance Gain Control
// ============================================================

`timescale 1ns/1ps

module awb_gain_control #(
    parameter int DATA_WIDTH = 12
) (
    input  logic                    clk_i,
    input  logic                    rst_n_i,
    input  logic                    cfg_enable_i,

    // RGB Input
    input  logic [23:0]             rgb_data_i,
    input  logic                    rgb_valid_i,

    // Statistics Output
    output logic [15:0]             awb_stats_r_o,
    output logic [15:0]             awb_stats_g_o,
    output logic [15:0]             awb_stats_b_o,

    // Computed Gains
    output logic [11:0]             awb_gain_r_o,
    output logic [11:0]             awb_gain_g_o,
    output logic [11:0]             awb_gain_b_o,
    output logic                    awb_done_o,

    // Configuration
    input  logic [11:0]             cfg_gain_r_i,
    input  logic [11:0]             cfg_gain_g_i,
    input  logic [11:0]             cfg_gain_b_i,
    input  logic                    cfg_manual_i
);

    // Grid configuration
    localparam int GRID_COLS = 32;
    localparam int GRID_ROWS = 32;
    localparam int PIXELS_PER_TILE = 64; // 4096 / 32

    // Accumulation registers
    logic [31:0]                    accum_r[GRID_ROWS][GRID_COLS];
    logic [31:0]                    accum_g[GRID_ROWS][GRID_COLS];
    logic [31:0]                    accum_b[GRID_ROWS][GRID_COLS];
    logic [15:0]                    pixel_count[GRID_ROWS][GRID_COLS];

    // Current grid position
    logic [5:0]                     grid_x;
    logic [5:0]                     grid_y;
    logic [15:0]                    pixel_in_tile;

    // Frame end detection
    logic                           frame_end;

    // Global statistics
    logic [31:0]                    total_r;
    logic [31:0]                    total_g;
    logic [31:0]                    total_b;
    logic [31:0]                    total_pixels;

    // AWB algorithm state
    typedef enum logic [1:0] {
        ACCUMULATE,
        COMPUTE,
        APPLY,
        IDLE
    } awb_state_t;

    awb_state_t                     awb_state;
    logic [15:0]                    tile_idx;
    logic [31:0]                    avg_r, avg_g, avg_b;
    logic [11:0]                    new_gain_r, new_gain_g, new_gain_b;

    // ============================================================
    // Grid-based Accumulation
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            grid_x <= '0;
            grid_y <= '0;
            pixel_in_tile <= '0;
            frame_end <= '0;
        end else if (rgb_valid_i) begin
            // Determine grid position
            grid_x <= pixel_in_tile / PIXELS_PER_TILE;
            grid_y <= pixel_in_tile / (GRID_COLS * PIXELS_PER_TILE);

            // Accumulate in current tile
            accum_r[grid_y][grid_x] <= accum_r[grid_y][grid_x] + rgb_data_i[23:16];
            accum_g[grid_y][grid_x] <= accum_g[grid_y][grid_x] + rgb_data_i[15:8];
            accum_b[grid_y][grid_x] <= accum_b[grid_y][grid_x] + rgb_data_i[7:0];
            pixel_count[grid_y][grid_x] <= pixel_count[grid_y][grid_x] + 1;

            pixel_in_tile <= pixel_in_tile + 1;

            if (pixel_in_tile == 16'hFFFF) begin
                frame_end <= '1;
            end
        end else begin
            frame_end <= '0;
        end
    end

    // ============================================================
    // Global Statistics
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            total_r <= '0;
            total_g <= '0;
            total_b <= '0;
            total_pixels <= '0;
        end else if (rgb_valid_i) begin
            total_r <= total_r + rgb_data_i[23:16];
            total_g <= total_g + rgb_data_i[15:8];
            total_b <= total_b + rgb_data_i[7:0];
            total_pixels <= total_pixels + 1;
        end
    end

    // ============================================================
    // AWB Computation
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            awb_state <= IDLE;
            awb_gain_r_o <= '0;
            awb_gain_g_o <= '0;
            awb_gain_b_o <= '0;
            awb_done_o <= '0;
        end else begin
            case (awb_state)
                IDLE: begin
                    if (frame_end) begin
                        awb_state <= COMPUTE;
                        tile_idx <= '0;
                    end
                    awb_done_o <= '0;
                end

                COMPUTE: begin
                    // Compute averages for current tile
                    if (pixel_count[tile_idx / GRID_COLS][tile_idx % GRID_COLS] > 0) begin
                        avg_r = accum_r[tile_idx / GRID_COLS][tile_idx % GRID_COLS] /
                                pixel_count[tile_idx / GRID_COLS][tile_idx % GRID_COLS];
                        avg_g = accum_g[tile_idx / GRID_COLS][tile_idx % GRID_COLS] /
                                pixel_count[tile_idx / GRID_COLS][tile_idx % GRID_COLS];
                        avg_b = accum_b[tile_idx / GRID_COLS][tile_idx % GRID_COLS] /
                                pixel_count[tile_idx / GRID_COLS][tile_idx % GRID_COLS];
                    end

                    tile_idx <= tile_idx + 1;

                    if (tile_idx == (GRID_ROWS * GRID_COLS - 1)) begin
                        awb_state <= APPLY;
                    end
                end

                APPLY: begin
                    if (!cfg_manual_i && cfg_enable_i) begin
                        // Gray world assumption - equalize channels
                        // Calculate gain to make average green
                        new_gain_g = 12'h1000; // 1.0x default

                        if (total_g > 0) begin
                            new_gain_r = (total_g * 12'h1000) / total_r;
                            new_gain_b = (total_g * 12'h1000) / total_b;
                        end else begin
                            new_gain_r = 12'h1000;
                            new_gain_b = 12'h1000;
                        end

                        awb_gain_r_o <= new_gain_r;
                        awb_gain_g_o <= new_gain_g;
                        awb_gain_b_o <= new_gain_b;
                    end else begin
                        awb_gain_r_o <= cfg_gain_r_i;
                        awb_gain_g_o <= cfg_gain_g_i;
                        awb_gain_b_o <= cfg_gain_b_i;
                    end

                    awb_done_o <= '1;
                    awb_state <= IDLE;
                end
            endcase
        end
    end

    // ============================================================
    // Statistics Output
    // ============================================================
    assign awb_stats_r_o = total_r[31:16];
    assign awb_stats_g_o = total_g[31:16];
    assign awb_stats_b_o = total_b[31:16];

endmodule
