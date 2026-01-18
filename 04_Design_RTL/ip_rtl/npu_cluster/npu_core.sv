//-----------------------------------------------------------------------------
// NPU Core Module
// File: npu_core.sv
// Description: Single NPU Core with MAC Array and Control Logic
//-----------------------------------------------------------------------------
// User: NPU RTL Design Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------

`timescale 1ns/1ps

module npu_core #
(
    parameter int DATA_WIDTH      = 512
)
(
    // Clock and Reset
    input  logic                  clk_i,
    input  logic                  rst_ni,
    input  logic                  enable_i,

    // Operation Configuration
    input  logic [3:0]            op_type_i,
    input  logic [15:0]           dim_n_i,
    input  logic [15:0]           dim_h_i,
    input  logic [15:0]           dim_w_i,
    input  logic [15:0]           dim_k_i,
    input  logic [15:0]           dim_c_i,
    input  logic [15:0]           stride_h_i,
    input  logic [15:0]           stride_w_i,
    input  logic [15:0]           pad_h_i,
    input  logic [15:0]           pad_w_i,
    input  logic                  start_i,

    // Memory Interface - Weight SRAM
    input  logic [DATA_WIDTH-1:0] weight_data_i [15:0],
    output logic                  weight_sram_clk_o,
    output logic                  weight_sram_csb_o,
    output logic [15:0]           weight_sram_addr_o,
    output logic [511:0]          weight_sram_wdata_o,
    output logic [63:0]           weight_sram_wmask_o,
    input  logic [511:0]          weight_sram_rdata_i,

    // Memory Interface - Activation SRAM
    input  logic [DATA_WIDTH-1:0] act_data_i [15:0],
    output logic                  act_sram_clk_o,
    output logic                  act_sram_csb_o,
    output logic [15:0]           act_sram_addr_o,
    output logic [511:0]          act_sram_wdata_o,
    output logic [63:0]           act_sram_wmask_o,
    input  logic [511:0]          act_sram_rdata_i,

    // Memory Interface - Output Buffer
    output logic [DATA_WIDTH-1:0] out_data_o [7:0],
    output logic                  out_sram_clk_o,
    output logic                  out_sram_csb_o,
    output logic [14:0]           out_sram_addr_o,
    output logic [511:0]          out_sram_wdata_o,
    output logic [63:0]           out_sram_wmask_o,
    input  logic [511:0]          out_sram_rdata_i,

    // Status
    output logic                  busy_o,
    output logic                  done_o,
    output logic [7:0]            error_o
);

    //-------------------------------------------------------------------------
    // Parameters
    //-------------------------------------------------------------------------
    localparam int MAC_ARRAY_SIZE   = 1024;
    localparam int NUM_BANKS        = 16;
    localparam int BANK_ADDR_WIDTH  = 16;
    localparam int OUT_BANK_ADDR    = 15;

    //-------------------------------------------------------------------------
    // Signals
    //-------------------------------------------------------------------------
    // MAC Array Signals
    logic [7:0]                     mac_weight_in [MAC_ARRAY_SIZE-1:0];
    logic [7:0]                     mac_act_in [MAC_ARRAY_SIZE-1:0];
    logic [31:0]                    mac_acc_out [MAC_ARRAY_SIZE-1:0];
    logic                           mac_valid_out;

    // Matrix Multiplication Unit Signals
    logic [7:0]                     mmu_weight_a [511:0];
    logic [7:0]                     mmu_act_b [511:0];
    logic [31:0]                    mmu_result_c [1023:0];
    logic                           mmu_valid;

    // Activation Unit Signals
    logic [31:0]                    act_input;
    logic [31:0]                    act_output;
    logic [3:0]                     act_type;
    logic                           act_valid;

    // Pooling Unit Signals
    logic [31:0]                    pool_input;
    logic [31:0]                    pool_output;
    logic [1:0]                     pool_type;
    logic [2:0]                     pool_kernel;
    logic                           pool_valid;

    // Tensor Buffer Signals
    logic                           tb_write_enable;
    logic [31:0]                    tb_write_addr;
    logic [31:0]                    tb_read_addr;
    logic [511:0]                   tb_write_data;
    logic [511:0]                   tb_read_data;

    // Scheduler Signals
    logic                           sched_enable;
    logic [15:0]                    sched_pc;
    logic                           sched_done;

    //-------------------------------------------------------------------------
    // Control Logic
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            busy_o      <= 1'b0;
            done_o      <= 1'b0;
            error_o     <= 8'b0;
        end else if (start_i && enable_i) begin
            busy_o      <= 1'b1;
            done_o      <= 1'b0;
            error_o     <= 8'b0;
        end else if (sched_done) begin
            busy_o      <= 1'b0;
            done_o      <= 1'b1;
        end
    end

    //-------------------------------------------------------------------------
    // MAC Array (1024 INT8 MACs)
    //-------------------------------------------------------------------------
    generate
        for (genvar i = 0; i < MAC_ARRAY_SIZE; i++) begin : GEN_MAC_ARRAY
            always_ff @(posedge clk_i) begin
                if (enable_i) begin
                    // Pipeline Stage 1: Input Latch
                    mac_weight_in[i] <= mmu_weight_a[i];
                    mac_act_in[i]    <= mmu_act_b[i];

                    // Pipeline Stage 2: Multiplication
                    logic [15:0] product;
                    product = $signed(mac_weight_in[i]) * $signed(mac_act_in[i]);

                    // Pipeline Stage 3: Accumulation
                    if (i == 0) begin
                        mac_acc_out[i] <= product;
                    end else begin
                        mac_acc_out[i] <= mac_acc_out[i-1] + product;
                    end
                end
            end
        end
    endgenerate

    //-------------------------------------------------------------------------
    // Matrix Multiplication Unit
    //-------------------------------------------------------------------------
    matrix_mult_unit u_matrix_mult (
        .clk_i              (clk_i),
        .rst_ni             (rst_ni),
        .enable_i           (enable_i),
        .weight_a_i         (mmu_weight_a),
        .act_b_i            (mmu_act_b),
        .result_c_o         (mmu_result_c),
        .valid_o            (mmu_valid)
    );

    //-------------------------------------------------------------------------
    // Activation Unit
    //-------------------------------------------------------------------------
    activation_unit u_activation (
        .clk_i              (clk_i),
        .rst_ni             (rst_ni),
        .enable_i           (enable_i),
        .act_type_i         (act_type),
        .data_i             (act_input),
        .data_o             (act_output),
        .valid_o            (act_valid)
    );

    //-------------------------------------------------------------------------
    // Pooling Unit
    //-------------------------------------------------------------------------
    pooling_unit u_pooling (
        .clk_i              (clk_i),
        .rst_ni             (rst_ni),
        .enable_i           (enable_i),
        .pool_type_i        (pool_type),
        .pool_kernel_i      (pool_kernel),
        .data_i             (pool_input),
        .data_o             (pool_output),
        .valid_o            (pool_valid)
    );

    //-------------------------------------------------------------------------
    // Tensor Buffer (Weight SRAM Interface)
    //-------------------------------------------------------------------------
    tensor_buffer #(
        .SIZE               (2097152),
        .DATA_WIDTH         (512),
        .ADDR_WIDTH         (16)
    ) u_tensor_buffer_w (
        .clk_i              (clk_i),
        .rst_ni             (rst_ni),
        .we_i               (weight_sram_csb_o),
        .addr_i             (weight_sram_addr_o),
        .wdata_i            (weight_sram_wdata_o),
        .wmask_i            (weight_sram_wmask_o),
        .rdata_o            (weight_sram_rdata_i)
    );

    //-------------------------------------------------------------------------
    // Tensor Buffer (Activation SRAM Interface)
    //-------------------------------------------------------------------------
    tensor_buffer #(
        .SIZE               (2097152),
        .DATA_WIDTH         (512),
        .ADDR_WIDTH         (16)
    ) u_tensor_buffer_a (
        .clk_i              (clk_i),
        .rst_ni             (rst_ni),
        .we_i               (act_sram_csb_o),
        .addr_i             (act_sram_addr_o),
        .wdata_i            (act_sram_wdata_o),
        .wmask_i            (act_sram_wmask_o),
        .rdata_o            (act_sram_rdata_i)
    );

    //-------------------------------------------------------------------------
    // Tensor Buffer (Output Buffer Interface)
    //-------------------------------------------------------------------------
    tensor_buffer #(
        .SIZE               (1048576),
        .DATA_WIDTH         (512),
        .ADDR_WIDTH         (15)
    ) u_tensor_buffer_o (
        .clk_i              (clk_i),
        .rst_ni             (rst_ni),
        .we_i               (out_sram_csb_o),
        .addr_i             (out_sram_addr_o),
        .wdata_i            (out_sram_wdata_o),
        .wmask_i            (out_sram_wmask_o),
        .rdata_o            (out_sram_rdata_i)
    );

    //-------------------------------------------------------------------------
    // Control Unit
    //-------------------------------------------------------------------------
    always_comb begin
        weight_sram_clk_o   = clk_i;
        weight_sram_csb_o   = 1'b1;
        weight_sram_addr_o  = '0;
        weight_sram_wdata_o = '0;
        weight_sram_wmask_o = '0;

        act_sram_clk_o      = clk_i;
        act_sram_csb_o      = 1'b1;
        act_sram_addr_o     = '0;
        act_sram_wdata_o    = '0;
        act_sram_wmask_o    = '0;

        out_sram_clk_o      = clk_i;
        out_sram_csb_o      = 1'b1;
        out_sram_addr_o     = '0;
        out_sram_wdata_o    = '0;
        out_sram_wmask_o    = '0;

        case (op_type_i)
            4'b0000: begin // Convolution
                weight_sram_csb_o = 1'b0;
                weight_sram_addr_o = dim_c_i[7:0];
                act_sram_csb_o = 1'b0;
                act_sram_addr_o = dim_h_i[7:0];
            end
            4'b0001: begin // Matrix Multiply
                weight_sram_csb_o = 1'b0;
                weight_sram_addr_o = dim_k_i[7:0];
                act_sram_csb_o = 1'b0;
                act_sram_addr_o = dim_c_i[7:0];
            end
            4'b0010: begin // Pooling
                out_sram_csb_o = 1'b0;
                out_sram_addr_o = dim_n_i[6:0];
            end
            4'b0011: begin // Activation
                act_sram_csb_o = 1'b0;
                act_sram_addr_o = dim_h_i[7:0];
                out_sram_csb_o = 1'b0;
                out_sram_addr_o = dim_h_i[6:0];
            end
            default: begin
                weight_sram_csb_o = 1'b1;
                act_sram_csb_o = 1'b1;
                out_sram_csb_o = 1'b1;
            end
        endcase
    end

    //-------------------------------------------------------------------------
    // Operation Selection Logic
    //-------------------------------------------------------------------------
    always_comb begin
        act_type = 4'b0000;
        pool_type = 2'b00;
        pool_kernel = 3'd2;

        case (op_type_i)
            4'b0000: begin // Convolution
                // Default conv parameters
            end
            4'b0011: begin // Activation
                act_type = 4'b0001; // ReLU
            end
            4'b0100: begin // Max Pooling
                pool_type = 2'b01; // Max
                pool_kernel = 3'd2;
            end
            4'b0101: begin // Average Pooling
                pool_type = 2'b10; // Avg
                pool_kernel = 3'd2;
            end
        endcase
    end

endmodule
