//-----------------------------------------------------------------------------
// Matrix Multiplication Unit
// File: matrix_mult_unit.sv
// Description: High-performance Matrix Multiplication Engine
//              Supports INT8 and FP16 precision
//-----------------------------------------------------------------------------
// User: NPU RTL Design Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------

`timescale 1ns/1ps

module matrix_mult_unit #
(
    parameter int DATA_WIDTH    = 512,
    parameter int MAC_COUNT     = 1024
)
(
    // Clock and Reset
    input  logic                  clk_i,
    input  logic                  rst_ni,
    input  logic                  enable_i,

    // Input Data - Weight Matrix A
    input  logic [7:0]            weight_a_i [511:0],

    // Input Data - Activation Matrix B
    input  logic [7:0]            act_b_i [511:0],

    // Output Data - Result Matrix C
    output logic [31:0]           result_c_o [1023:0],

    // Control
    output logic                  valid_o
);

    //-------------------------------------------------------------------------
    // Parameters
    //-------------------------------------------------------------------------
    localparam int ROWS_A         = 32;
    localparam int COLS_A         = 32;
    localparam int COLS_B         = 32;
    localparam int MATRIX_SIZE    = 1024;

    //-------------------------------------------------------------------------
    // Signals
    //-------------------------------------------------------------------------
    // Pipeline registers
    logic [7:0]                   pipe_weight_a [MATRIX_SIZE-1:0][3:0];
    logic [7:0]                   pipe_act_b [MATRIX_SIZE-1:0][3:0];
    logic [15:0]                  pipe_product [MATRIX_SIZE-1:0][3:0];
    logic [31:0]                  pipe_accum [MATRIX_SIZE-1:0][4:0];

    // Partial sum selection
    logic [1:0]                   accum_stage;

    //-------------------------------------------------------------------------
    // Input Pipeline Stage 0
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i) begin
        if (enable_i) begin
            for (int i = 0; i < MATRIX_SIZE; i++) begin
                pipe_weight_a[i][0] <= weight_a_i[i];
                pipe_act_b[i][0]    <= act_b_i[i];
            end
        end
    end

    //-------------------------------------------------------------------------
    // Multiplication Stage (Pipeline Stage 1)
    //-------------------------------------------------------------------------
    generate
        for (genvar i = 0; i < MATRIX_SIZE; i++) begin : GEN_MULT
            always_ff @(posedge clk_i) begin
                if (enable_i) begin
                    pipe_product[i][0] <= $signed(pipe_weight_a[i][0]) * $signed(pipe_act_b[i][0]);
                end
            end
        end
    endgenerate

    //-------------------------------------------------------------------------
    // First Level Accumulation (Pipeline Stage 2)
    //-------------------------------------------------------------------------
    generate
        for (genvar i = 0; i < MATRIX_SIZE/2; i++) begin : GEN_ACCUM_L1
            always_ff @(posedge clk_i) begin
                if (enable_i) begin
                    pipe_product[i*2][1] <= pipe_product[i*2][0];
                    pipe_product[i*2+1][1] <= pipe_product[i*2+1][0];
                    pipe_accum[i][1] <= $signed(pipe_product[i*2][0]) + $signed(pipe_product[i*2+1][0]);
                end
            end
        end
    endgenerate

    //-------------------------------------------------------------------------
    // Second Level Accumulation (Pipeline Stage 3)
    //-------------------------------------------------------------------------
    generate
        for (genvar i = 0; i < MATRIX_SIZE/4; i++) begin : GEN_ACCUM_L2
            always_ff @(posedge clk_i) begin
                if (enable_i) begin
                    pipe_accum[i*2][2] <= pipe_accum[i*2][1];
                    pipe_accum[i*2+1][2] <= pipe_accum[i*2+1][1];
                    pipe_accum[i][2] <= $signed(pipe_accum[i*2][1]) + $signed(pipe_accum[i*2+1][1]);
                end
            end
        end
    endgenerate

    //-------------------------------------------------------------------------
    // Third Level Accumulation (Pipeline Stage 4)
    //-------------------------------------------------------------------------
    generate
        for (genvar i = 0; i < MATRIX_SIZE/8; i++) begin : GEN_ACCUM_L3
            always_ff @(posedge clk_i) begin
                if (enable_i) begin
                    pipe_accum[i*2][3] <= pipe_accum[i*2][2];
                    pipe_accum[i*2+1][3] <= pipe_accum[i*2+1][2];
                    pipe_accum[i][3] <= $signed(pipe_accum[i*2][2]) + $signed(pipe_accum[i*2+1][2]);
                end
            end
        end
    endgenerate

    //-------------------------------------------------------------------------
    // Fourth Level Accumulation (Pipeline Stage 5)
    //-------------------------------------------------------------------------
    generate
        for (genvar i = 0; i < MATRIX_SIZE/16; i++) begin : GEN_ACCUM_L4
            always_ff @(posedge clk_i) begin
                if (enable_i) begin
                    pipe_accum[i*2][4] <= pipe_accum[i*2][3];
                    pipe_accum[i*2+1][4] <= pipe_accum[i*2+1][3];
                    pipe_accum[i][4] <= $signed(pipe_accum[i*2][3]) + $signed(pipe_accum[i*2+1][3]);
                end
            end
        end
    endgenerate

    //-------------------------------------------------------------------------
    // Output Assignment
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i) begin
        if (enable_i) begin
            for (int i = 0; i < MATRIX_SIZE/16; i++) begin
                result_c_o[i] <= pipe_accum[i][4];
            end
            valid_o <= enable_i;
        end else begin
            valid_o <= 1'b0;
        end
    end

    //-------------------------------------------------------------------------
    // Sparse Computation Support
    //-------------------------------------------------------------------------
    generate
        for (genvar i = 0; i < MATRIX_SIZE; i++) begin : GEN_SPARSE_CHECK
            logic [7:0] weight_z;
            logic [7:0] act_z;

            assign weight_z = (pipe_weight_a[i][0] == 8'b0);
            assign act_z = (pipe_act_b[i][0] == 8'b0);

            // Skip multiplication if either operand is zero
            always_ff @(posedge clk_i) begin
                if (weight_z || act_z) begin
                    pipe_product[i][0] <= 16'b0;
                end
            end
        end
    endgenerate

endmodule
