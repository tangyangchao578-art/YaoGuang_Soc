// ============================================================
// Project: YaoGuang ISP
// Module:  bayer_processing.sv
// Description: Bayer Processing (BLC, DPC, LSC, WB)
// ============================================================

`timescale 1ns/1ps

module bayer_processing #(
    parameter int DATA_WIDTH = 16
) (
    input  logic                    clk_i,
    input  logic                    rst_n_i,

    // Configuration
    input  logic                    cfg_enable_i,
    input  logic [7:0]              cfg_offset_i,
    input  logic                    cfg_dpc_enable_i,
    input  logic [15:0]             cfg_dpc_threshold_i,
    input  logic                    cfg_lsc_enable_i,
    input  logic [11:0]             cfg_lsc_gain_red[17][17],
    input  logic [11:0]             cfg_lsc_gain_green[17][17],
    input  logic [11:0]             cfg_lsc_gain_blue[17][17],
    input  logic                    cfg_wb_enable_i,
    input  logic [11:0]             cfg_wb_gain_r,
    input  logic [11:0]             cfg_wb_gain_g,
    input  logic [11:0]             cfg_wb_gain_b,

    // Input
    input  logic [DATA_WIDTH-1:0]   raw_data_i,
    input  logic                    raw_valid_i,
    input  logic                    raw_sop_i,
    input  logic                    raw_eop_i,

    // Outputs
    output logic [DATA_WIDTH-1:0]   blc_data_o,
    output logic                    blc_valid_o,
    output logic [DATA_WIDTH-1:0]   dpc_data_o,
    output logic                    dpc_valid_o,
    output logic [DATA_WIDTH-1:0]   lsc_data_o,
    output logic                    lsc_valid_o,
    output logic [23:0]             wb_data_o,
    output logic                    wb_valid_o
);

    // Line Buffer for DPC
    localparam int LINE_BUFFER_SIZE = 4096;
    logic [DATA_WIDTH-1:0]          line_buffer[2][LINE_BUFFER_SIZE];
    logic [12:0]                    buffer_addr;
    logic [2:0]                     row_counter;
    logic                           buffer_write;

    // Pixel Position
    logic [12:0]                    pixel_x;
    logic [12:0]                    pixel_y;
    logic                           frame_active;

    // ============================================================
    // Black Level Correction
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            blc_data_o <= '0;
            blc_valid_o <= '0;
        end else if (raw_valid_i) begin
            if (cfg_enable_i) begin
                // Subtract black level offset
                if (raw_data_i > cfg_offset_i) begin
                    blc_data_o <= raw_data_i - cfg_offset_i;
                end else begin
                    blc_data_o <= '0;
                end
            end else begin
                blc_data_o <= raw_data_i;
            end
            blc_valid_o <= '1;
        end else begin
            blc_valid_o <= '0;
        end
    end

    // ============================================================
    // Defect Pixel Correction
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            dpc_data_o <= '0;
            dpc_valid_o <= '0;
            row_counter <= '0;
            buffer_addr <= '0;
        end else begin
            dpc_valid_o <= blc_valid_o;

            if (blc_valid_o) begin
                // Line buffer management
                if (pixel_x == 0) begin
                    row_counter <= (row_counter == 2) ? 0 : row_counter + 1;
                end

                // Store current pixel in buffer
                line_buffer[row_counter][pixel_x] <= blc_data_o;

                if (cfg_dpc_enable_i && pixel_x > 0 && pixel_x < 4095) begin
                    // Gradient-based defect detection
                    logic [15:0] grad_h, grad_v, grad_d1, grad_d2;
                    logic [15:0] center, up, down, left, right;

                    up    = line_buffer[(row_counter == 0) ? 2 : row_counter-1][pixel_x];
                    down  = line_buffer[(row_counter == 2) ? 0 : row_counter+1][pixel_x];
                    left  = line_buffer[row_counter][pixel_x-1];
                    right = line_buffer[row_counter][pixel_x+1];
                    center = blc_data_o;

                    grad_h = $abs(right - left);
                    grad_v = $abs(up - down);
                    grad_d1 = $abs(line_buffer[(row_counter == 0) ? 2 : row_counter-1][pixel_x-1] -
                                   line_buffer[(row_counter == 2) ? 0 : row_counter+1][pixel_x+1]);
                    grad_d2 = $abs(line_buffer[(row_counter == 0) ? 2 : row_counter-1][pixel_x+1] -
                                   line_buffer[(row_counter == 2) ? 0 : row_counter+1][pixel_x-1]);

                    if ($abs(center - up) > cfg_dpc_threshold_i &&
                        $abs(center - down) > cfg_dpc_threshold_i &&
                        $abs(center - left) > cfg_dpc_threshold_i &&
                        $abs(center - right) > cfg_dpc_threshold_i) begin
                        // Defective pixel detected, use average
                        dpc_data_o <= (up + down + left + right) >> 2;
                    end else begin
                        dpc_data_o <= center;
                    end
                end else begin
                    dpc_data_o <= blc_data_o;
                end

                // Update position
                if (raw_eop_i) begin
                    pixel_x <= '0;
                    pixel_y <= pixel_y + 1;
                end else begin
                    pixel_x <= pixel_x + 1;
                end
            end

            if (raw_sop_i) begin
                pixel_x <= '0;
                pixel_y <= '0;
                row_counter <= '0;
            end
        end
    end

    // ============================================================
    // Lens Shading Correction
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            lsc_data_o <= '0;
            lsc_valid_o <= '0;
        end else if (dpc_valid_o) begin
            lsc_valid_o <= '1;

            if (cfg_lsc_enable_i) begin
                // Determine color channel based on Bayer pattern position
                logic [1:0] channel;
                logic [11:0] gain[3];

                channel = {(pixel_y[0] ^ pixel_x[0]), pixel_x[0]};
                gain = cfg_lsc_gain_red[pixel_y[7:4]][pixel_x[7:4]];

                // Apply LSC gain
                case (channel)
                    2'b00: lsc_data_o <= (dpc_data_o * gain[0]) >> 12;
                    2'b01: lsc_data_o <= (dpc_data_o * gain[1]) >> 12;
                    2'b10: lsc_data_o <= (dpc_data_o * gain[1]) >> 12;
                    2'b11: lsc_data_o <= (dpc_data_o * gain[2]) >> 12;
                endcase
            end else begin
                lsc_data_o <= dpc_data_o;
            end
        end else begin
            lsc_valid_o <= '0;
        end
    end

    // ============================================================
    // White Balance
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            wb_data_o <= '0;
            wb_valid_o <= '0;
        end else if (lsc_valid_o) begin
            wb_valid_o <= '1;

            if (cfg_wb_enable_i) begin
                logic [1:0] channel;
                logic [23:0] scaled_pixel;

                scaled_pixel = {lsc_data_o, 8'h00};
                channel = {(pixel_y[0] ^ pixel_x[0]), pixel_x[0]};

                case (channel)
                    2'b00: wb_data_o <= (scaled_pixel * cfg_wb_gain_r) >> 12;
                    2'b01: wb_data_o <= (scaled_pixel * cfg_wb_gain_g) >> 12;
                    2'b10: wb_data_o <= (scaled_pixel * cfg_wb_gain_g) >> 12;
                    2'b11: wb_data_o <= (scaled_pixel * cfg_wb_gain_b) >> 12;
                endcase
            end else begin
                wb_data_o <= {lsc_data_o, 8'h00};
            end
        end else begin
            wb_valid_o <= '0;
        end
    end

endmodule
