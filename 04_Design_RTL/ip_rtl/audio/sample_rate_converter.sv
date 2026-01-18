// Copyright (c) 2026 YaoGuang SoC Project
// All rights reserved

// Sample Rate Converter Module
// Revision: 1.0
// Date: 2026-01-18

`timescale 1ns/1ps

module sample_rate_converter (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         enable,

    // PCM Data Interface
    input  wire [31:0]  pcm_din,
    input  wire         pcm_din_valid,
    output wire [31:0]  pcm_dout,
    output wire         pcm_dout_valid
);

    // Parameters
    localparam DATA_WIDTH = 24;
    localparam ACC_WIDTH  = 32;
    localparam FILT_TAPS  = 64;
    localparam PHASE_NUM  = 256;

    // Control Register
    reg  [31:0]  ctrl_reg;

    // Internal Signals
    reg  [15:0]  input_rate;
    reg  [15:0]  output_rate;
    reg          bypass;
    reg          async_mode;

    // Accumulator for fractional interpolation
    reg  [ACC_WIDTH-1:0] acc;
    wire [ACC_WIDTH-1:0] inc;

    // Input FIFO
    reg  [DATA_WIDTH-1:0] input_fifo [63:0];
    reg  [5:0]   input_wr_ptr;
    reg  [5:0]   input_rd_ptr;
    reg  [6:0]   input_fifo_count;
    wire        input_fifo_full;
    wire        input_fifo_empty;

    // Output FIFO
    reg  [DATA_WIDTH-1:0] output_fifo [63:0];
    reg  [5:0]   output_wr_ptr;
    reg  [5:0]   output_rd_ptr;
    reg  [6:0]   output_fifo_count;
    wire        output_fifo_full;
    wire        output_fifo_empty;

    // FIR Filter Coefficients (polyphase)
    reg  [17:0]  coeffs [FILT_TAPS-1:0];

    // Interpolation
    wire [47:0]  interpolation_sum;

    // Input rate monitoring
    reg  [31:0]  sample_cnt;
    reg  [31:0]  rate_measure;

    // Initialize coefficients (sinc-based interpolation filter)
    integer i;
    initial begin
        for (i = 0; i < FILT_TAPS; i = i + 1) begin
            coeffs[i] = 18'd0;
        end
        // Coefficients will be loaded via register or use default values
        coeffs[0]  = 18'sh00000;
        coeffs[8]  = 18'sh00001;
        coeffs[16] = 18'sh00005;
        coeffs[24] = 18'sh0000E;
        coeffs[32] = 18'sh00100;
    end

    // Input FIFO control
    assign input_fifo_full  = (input_fifo_count == 7'd64);
    assign input_fifo_empty = (input_fifo_count == 7'd0);

    always @(posedge clk) begin
        if (!rst_n) begin
            input_wr_ptr <= 6'd0;
            input_rd_ptr <= 6'd0;
            input_fifo_count <= 7'd0;
        end else if (!enable) begin
            input_wr_ptr <= 6'd0;
            input_rd_ptr <= 6'd0;
            input_fifo_count <= 7'd0;
        end else begin
            if (pcm_din_valid && !input_fifo_full) begin
                input_fifo[input_wr_ptr] <= pcm_din[DATA_WIDTH-1:0];
                input_wr_ptr <= input_wr_ptr + 1'b1;
                input_fifo_count <= input_fifo_count + 1'b1;
            end

            if (async_mode && !input_fifo_empty) begin
                input_rd_ptr <= input_rd_ptr + 1'b1;
                input_fifo_count <= input_fifo_count - 1'b1;
            end
        end
    end

    // Output FIFO control
    assign output_fifo_full  = (output_fifo_count == 7'd64);
    assign output_fifo_empty = (output_fifo_count == 7'd0);

    always @(posedge clk) begin
        if (!rst_n) begin
            output_wr_ptr <= 6'd0;
            output_rd_ptr <= 6'd0;
            output_fifo_count <= 7'd0;
        end else if (!enable) begin
            output_wr_ptr <= 6'd0;
            output_rd_ptr <= 6'd0;
            output_fifo_count <= 7'd0;
        end else begin
            if (interpolation_valid && !output_fifo_full) begin
                output_fifo[output_wr_ptr] <= interpolation_result[DATA_WIDTH-1:0];
                output_wr_ptr <= output_wr_ptr + 1'b1;
                output_fifo_count <= output_fifo_count + 1'b1;
            end

            if (!output_fifo_empty) begin
                output_rd_ptr <= output_rd_ptr + 1'b1;
                output_fifo_count <= output_fifo_count - 1'b1;
            end
        end
    end

    // Increment calculation
    assign inc = (async_mode) ?
                 ({16'd0, output_rate} << 16) / {16'd0, input_rate} :
                 32'd1 << 20;

    // Asynchronous mode accumulator
    always @(posedge clk) begin
        if (!rst_n) begin
            acc <= 32'd0;
        end else if (!enable) begin
            acc <= 32'd0;
        end else begin
            if (async_mode) begin
                acc <= acc + inc;
                if (acc[31:24] != 8'd0) begin
                    acc <= acc[23:0];
                end
            end else begin
                acc <= acc + inc;
            end
        end
    end

    // Polyphase interpolation
    wire [7:0]   phase;
    wire [5:0]   tap;
    wire         interpolation_valid;
    wire [DATA_WIDTH-1:0] interpolation_result;

    assign phase = acc[ACC_WIDTH-1:ACC_WIDTH-8];
    assign tap   = acc[ACC_WIDTH-9:ACC_WIDTH-14];
    assign interpolation_valid = (acc[ACC_WIDTH-15] && !bypass && enable);

    // FIR interpolation filter
    reg  [47:0]  sum;
    integer      j;

    always @(*) begin
        sum = 48'd0;
        for (j = 0; j < FILT_TAPS; j = j + 1) begin
            if ((tap + j) < 6'd64) begin
                sum = sum + $signed(input_fifo[tap + j]) * $signed(coeffs[j]);
            end
        end
    end

    assign interpolation_result = sum[47:24];

    // Bypass path
    reg  [DATA_WIDTH-1:0] bypass_data;
    reg                    bypass_valid;

    always @(posedge clk) begin
        if (!enable || bypass) begin
            bypass_data <= pcm_din[DATA_WIDTH-1:0];
            bypass_valid <= pcm_din_valid;
        end else begin
            bypass_data <= 24'd0;
            bypass_valid <= 1'b0;
        end
    end

    // Output selection
    always @(posedge clk) begin
        if (!enable) begin
            pcm_dout <= 32'd0;
            pcm_dout_valid <= 1'b0;
        end else if (bypass) begin
            pcm_dout <= {{8{bypass_data[23]}}, bypass_data};
            pcm_dout_valid <= bypass_valid;
        end else begin
            pcm_dout <= {{8{interpolation_result[23]}}, interpolation_result};
            pcm_dout_valid <= interpolation_valid;
        end
    end

    // Rate measurement (for async mode)
    always @(posedge clk) begin
        if (!rst_n) begin
            sample_cnt <= 32'd0;
            rate_measure <= 32'd0;
        end else if (!enable) begin
            sample_cnt <= 32'd0;
        end else begin
            sample_cnt <= sample_cnt + 1'b1;
            if (sample_cnt == 32'd1000000) begin
                rate_measure <= input_fifo_count;
                sample_cnt <= 32'd0;
            end
        end
    end

    // Control Register
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ctrl_reg <= 32'd0;
        end else begin
            if (pwrite && psel && penable) begin
                if (paddr == 8'h40) begin
                    ctrl_reg <= pwdata[31:0];
                end
            end
        end
    end

    // Decode control fields
    always @(posedge clk) begin
        input_rate   <= ctrl_reg[15:0];
        output_rate  <= ctrl_reg[31:16];
        bypass       <= ctrl_reg[0];
        async_mode   <= ctrl_reg[1];
    end

endmodule
