// ============================================================
// Project: YaoGuang ISP
// Module:  output_formatter.sv
// Description: Output Formatter (YUV/RGB conversion)
// ============================================================

`timescale 1ns/1ps

module output_formatter #(
    parameter int DATA_WIDTH = 12,
    parameter int MAX_WIDTH = 3840,
    parameter int MAX_HEIGHT = 2160
) (
    input  logic                    clk_i,
    input  logic                    rst_n_i,
    input  logic [1:0]              cfg_format_i,

    // RGB Input
    input  logic [23:0]             rgb_data_i,
    input  logic                    rgb_valid_i,

    // Formatted Output
    output logic [DATA_WIDTH-1:0]   out_data_o,
    output logic                    out_valid_o,
    input  logic                    out_ready_i,

    // Pixel Position
    output logic [23:0]             out_pixel_x_o,
    output logic [23:0]             out_pixel_y_o,
    output logic                    out_frame_start_o,
    output logic                    out_frame_end_o
);

    // Output format encoding
    localparam [1:0] FMT_RAW16  = 2'b00;
    localparam [1:0] FMT_RGB24  = 2'b01;
    localparam [1:0] FMT_RGB30  = 2'b10;
    localparam [1:0] FMT_YUV422 = 2'b11;
    localparam [1:0] FMT_YUV420 = 2'b100;

    // Pixel position counters
    logic [12:0]                    pixel_x;
    logic [12:0]                    pixel_y;
    logic                           frame_start;
    logic                           frame_end;

    // Pipeline for format conversion
    logic [23:0]                    rgb_reg;
    logic                           valid_reg;
    logic [1:0]                     format_reg;

    // YUV conversion coefficients (BT.601)
    localparam [11:0] YUV_COEFF[5] = '{
        12'h1000,  // Y_R:  0.299
        12'h0811,  // Y_G:  0.587
        12'h03C8,  // Y_B:  0.114
        12'h1E80,  // U_R: -0.169
        12'h1E80   // V_B: -0.169
    };

    // Output FIFOs for different formats
    logic [DATA_WIDTH-1:0]          yuv422_fifo[2][1024];
    logic [9:0]                     yuv422_write_idx;
    logic [9:0]                     yuv422_read_idx;
    logic                           yuv422_valid;

    // ============================================================
    // Pixel Position Tracking
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            pixel_x <= '0;
            pixel_y <= '0;
            frame_start <= '1;
        end else if (rgb_valid_i) begin
            if (pixel_x == MAX_WIDTH - 1) begin
                pixel_x <= '0;
                if (pixel_y == MAX_HEIGHT - 1) begin
                    pixel_y <= '0;
                    frame_start <= '1;
                end else begin
                    pixel_y <= pixel_y + 1;
                    frame_start <= '0;
                end
            end else begin
                pixel_x <= pixel_x + 1;
                frame_start <= '0;
            end
        end
    end

    // ============================================================
    // Input Pipeline
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            rgb_reg <= '0;
            valid_reg <= '0;
            format_reg <= FMT_RGB24;
        end else if (rgb_valid_i) begin
            rgb_reg <= rgb_data_i;
            valid_reg <= '1;
            format_reg <= cfg_format_i;
        end else begin
            valid_reg <= '0;
        end
    end

    // ============================================================
    // Format Conversion
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            out_data_o <= '0;
            out_valid_o <= '0;
            out_pixel_x_o <= '0;
            out_pixel_y_o <= '0;
            out_frame_start_o <= '0;
            out_frame_end_o <= '0;
        end else begin
            out_frame_start_o <= frame_start;
            out_frame_end_o <= (pixel_x == MAX_WIDTH - 1) && (pixel_y == MAX_HEIGHT - 1);
            out_pixel_x_o <= pixel_x;
            out_pixel_y_o <= pixel_y;

            if (valid_reg && out_ready_i) begin
                case (format_reg)
                    FMT_RAW16: begin
                        // Output raw 16-bit (red channel as example)
                        out_data_o <= rgb_reg[23:8];
                        out_valid_o <= '1;
                    end

                    FMT_RGB24: begin
                        // Output RGB24
                        out_data_o <= rgb_reg[23:8];
                        out_valid_o <= '1;
                    end

                    FMT_RGB30: begin
                        // Output RGB30 (10-bit per channel)
                        out_data_o <= {rgb_reg[23:18], rgb_reg[15:10], rgb_reg[7:2]};
                        out_valid_o <= '1;
                    end

                    FMT_YUV422: begin
                        // RGB to YUV422 conversion
                        logic [15:0] r, g, b;
                        logic [15:0] y, u, v;

                        r = rgb_reg[23:16];
                        g = rgb_reg[15:8];
                        b = rgb_reg[7:0];

                        // Y = 0.299*R + 0.587*G + 0.114*B
                        y = (r * YUV_COEFF[0] + g * YUV_COEFF[1] + b * YUV_COEFF[2]) >> 12;

                        // U = -0.169*R - 0.587*G + 0.500*B
                        u = ((b - g) * 12'h0800) >> 12;

                        // V = 0.500*R - 0.419*G - 0.081*B
                        v = ((r - g) * 12'h0800) >> 12;

                        // Store U/V for interleaved output
                        if (pixel_x[0] == 0) begin
                            // Y component
                            out_data_o <= y[15:0];
                            out_valid_o <= '1;
                        end else begin
                            // UV interleaved
                            out_data_o <= {u[7:0], v[7:0]};
                            out_valid_o <= '1;
                        end
                    end

                    FMT_YUV420: begin
                        // YUV420 requires downsampling U and V
                        // Store current line's U/V for next line averaging
                        out_data_o <= '0;
                        out_valid_o <= '0;
                    end

                    default: begin
                        out_data_o <= '0;
                        out_valid_o <= '0;
                    end
                endcase
            end else begin
                out_valid_o <= '0;
            end
        end
    end

endmodule
