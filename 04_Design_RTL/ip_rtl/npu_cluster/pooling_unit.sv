//-----------------------------------------------------------------------------
// Pooling Unit
// File: pooling_unit.sv
// Description: Max and Average Pooling Unit
//              Supports configurable kernel size, stride, and padding
//-----------------------------------------------------------------------------
// User: NPU RTL Design Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------

`timescale 1ns/1ps

module pooling_unit #
(
    parameter int DATA_WIDTH     = 32,
    parameter int MAX_KERNEL     = 8
)
(
    // Clock and Reset
    input  logic                  clk_i,
    input  logic                  rst_ni,
    input  logic                  enable_i,

    // Pooling Configuration
    // 00: Max Pooling, 01: Average Pooling, 10: Global, 11: Reserved
    input  logic [1:0]            pool_type_i,
    input logic [2:0]             pool_kernel_i,   // Kernel size: 1-8
    input logic [2:0]             pool_stride_i,   // Stride: 1-8
    input logic [2:0]             pool_pad_i,      // Padding: 0-7

    // Input Data
    input  logic [DATA_WIDTH-1:0] data_i,

    // Output Data
    output logic [DATA_WIDTH-1:0] data_o,

    // Control
    output logic                  valid_o
);

    //-------------------------------------------------------------------------
    // Parameters
    //-------------------------------------------------------------------------
    localparam int BUFFER_DEPTH   = 64;
    localparam int ADDR_WIDTH     = 6;

    //-------------------------------------------------------------------------
    // Signals
    //-------------------------------------------------------------------------
    // Line buffer for window formation
    logic [DATA_WIDTH-1:0]        line_buffer [3:0][BUFFER_DEPTH-1:0];
    logic [ADDR_WIDTH-1:0]        line_buffer_wr_addr;
    logic [ADDR_WIDTH-1:0]        line_buffer_rd_addr;

    // Window registers
    logic [DATA_WIDTH-1:0]        window_reg [7:0][7:0];
    logic [2:0]                   window_row;
    logic [2:0]                   window_col;

    // Comparison results
    logic [7:0]                   max_comparison [7:0];
    logic [7:0]                   max_valid;
    logic [DATA_WIDTH-1:0]        max_result;
    logic [DATA_WIDTH-1:0]        avg_result;
    logic [31:0]                 sum_accum;

    // Pooling state machine
    typedef enum logic [2:0] {
        POOL_IDLE,
        POOL_FILL,
        POOL_COMPUTE,
        POOL_DRAIN,
        POOL_DONE
    } pool_state_t;

    pool_state_t                  pool_state;
    pool_state_t                  next_state;

    logic [2:0]                   kernel_cnt;
    logic [2:0]                   stride_cnt;
    logic [15:0]                  pixel_counter;
    logic                         window_valid;

    //-------------------------------------------------------------------------
    // Line Buffer Logic
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i) begin
        if (enable_i) begin
            // Write to line buffer
            line_buffer[0][line_buffer_wr_addr] <= data_i;

            // Circular buffer behavior
            if (line_buffer_wr_addr == BUFFER_DEPTH - 1) begin
                line_buffer_wr_addr <= '0;
            end else begin
                line_buffer_wr_addr <= line_buffer_wr_addr + 1;
            end
        end
    end

    //-------------------------------------------------------------------------
    // Window Formation
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i) begin
        if (enable_i) begin
            // Read from line buffer with delay
            line_buffer[1][line_buffer_rd_addr] <= line_buffer[0][line_buffer_wr_addr];
            line_buffer[2][line_buffer_rd_addr] <= line_buffer[1][line_buffer_wr_addr];
            line_buffer[3][line_buffer_rd_addr] <= line_buffer[2][line_buffer_wr_addr];

            if (line_buffer_rd_addr == BUFFER_DEPTH - 1) begin
                line_buffer_rd_addr <= '0;
            end else begin
                line_buffer_rd_addr <= line_buffer_rd_addr + 1;
            end
        end
    end

    //-------------------------------------------------------------------------
    // Max Pooling Comparator Tree
    //-------------------------------------------------------------------------
    generate
        for (genvar row = 0; row < 8; row++) begin : GEN_MAX_ROW
            for (genvar col = 0; col < 8; col++) begin : GEN_MAX_COL
                always_comb begin
                    if (window_reg[row][col] > max_result) begin
                        max_comparison[row] = 1'b1;
                    end else begin
                        max_comparison[row] = 1'b0;
                    end
                end
            end
        end
    endgenerate

    //-------------------------------------------------------------------------
    // Max Pooling Result Selection
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i) begin
        if (enable_i) begin
            max_result <= '0;
            for (int row = 0; row < 8; row++) begin
                for (int col = 0; col < 8; col++) begin
                    if (row == 0 && col == 0) begin
                        max_result <= window_reg[row][col];
                    end else if (window_reg[row][col] > max_result) begin
                        max_result <= window_reg[row][col];
                    end
                end
            end
        end
    end

    //-------------------------------------------------------------------------
    // Average Pooling Accumulator
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i) begin
        if (enable_i) begin
            if (window_valid) begin
                sum_accum <= sum_accum + data_i;
                kernel_cnt <= kernel_cnt + 1;
            end

            if (kernel_cnt == pool_kernel_i) begin
                avg_result <= sum_accum / (1 << pool_kernel_i);
                sum_accum <= '0;
                kernel_cnt <= '0;
            end
        end
    end

    //-------------------------------------------------------------------------
    // Output Selection
    //-------------------------------------------------------------------------
    always_comb begin
        case (pool_type_i)
            2'b00: begin // Max Pooling
                data_o = max_result;
            end
            2'b01: begin // Average Pooling
                data_o = avg_result;
            end
            2'b10: begin // Global Pooling (reduce to single value)
                data_o = max_result;
            end
            default: begin
                data_o = data_i;
            end
        endcase
    end

    //-------------------------------------------------------------------------
    // Pooling State Machine
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            pool_state <= POOL_IDLE;
        end else begin
            pool_state <= next_state;
        end
    end

    always_comb begin
        next_state = pool_state;
        window_valid = 1'b0;
        valid_o = 1'b0;

        case (pool_state)
            POOL_IDLE: begin
                if (enable_i) begin
                    next_state = POOL_FILL;
                end
            end

            POOL_FILL: begin
                // Fill window buffer
                if (pixel_counter < {1'b0, pool_kernel_i, 3'b0}) begin
                    pixel_counter <= pixel_counter + 1;
                end else begin
                    next_state = POOL_COMPUTE;
                end
            end

            POOL_COMPUTE: begin
                window_valid = 1'b1;

                if (stride_cnt == pool_stride_i) begin
                    stride_cnt <= '0;
                    valid_o = 1'b1;
                    // Move to next window position
                    if (window_col < pool_kernel_i - 1) begin
                        window_col <= window_col + 1;
                    end else begin
                        window_col <= '0;
                        if (window_row < pool_kernel_i - 1) begin
                            window_row <= window_row + 1;
                        end else begin
                            next_state = POOL_DRAIN;
                        end
                    end
                end else begin
                    stride_cnt <= stride_cnt + 1;
                end
            end

            POOL_DRAIN: begin
                valid_o = 1'b1;
                next_state = POOL_DONE;
            end

            POOL_DONE: begin
                next_state = POOL_IDLE;
            end

            default: begin
                next_state = POOL_IDLE;
            end
        endcase
    end

    //-------------------------------------------------------------------------
    // Global Pooling Support
    //-------------------------------------------------------------------------
    generate
        if (MAX_KERNEL > 1) begin : GEN_GLOBAL_POOL
            always_ff @(posedge clk_i) begin
                if (enable_i) begin
                    // Track if this is global pooling
                    if (pool_type_i == 2'b10) begin
                        // Accumulate all elements for global average
                        sum_accum <= sum_accum + data_i;
                        pixel_counter <= pixel_counter + 1;

                        if (data_i > max_result) begin
                            max_result <= data_i;
                        end
                    end
                end
            end
        end
    endgenerate

endmodule
