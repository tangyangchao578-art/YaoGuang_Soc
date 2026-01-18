//-----------------------------------------------------------------------------
// NPU Cluster Top Module
// File: npu_cluster_top.sv
// Description: NPU Cluster Top-Level Integration
//              75 TOPS INT8 Computing Engine
//-----------------------------------------------------------------------------
// User: NPU RTL Design Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------

`timescale 1ns/1ps

module npu_cluster_top #
(
    parameter int NUM_CORES          = 1,
    parameter int ID_WIDTH           = 8,
    parameter int ADDR_WIDTH         = 32,
    parameter int DATA_WIDTH         = 512,
    parameter int WEIGHT_SRAM_SIZE   = 2097152,
    parameter int ACT_SRAM_SIZE      = 2097152,
    parameter int OUTPUT_BUF_SIZE    = 1048576
)
(
    // Clock and Reset
    input  logic                        clk_i,
    input  logic                        rst_ni,
    input  logic                        clk_gate_en_i,

    // NoC Interface - Read Channel
    input  logic [DATA_WIDTH-1:0]       noc_rdata_i,
    input  logic                        noc_rvalid_i,
    output logic [ID_WIDTH-1:0]         noc_rid_o,
    output logic [ADDR_WIDTH-1:0]       noc_araddr_o,
    output logic                        noc_arvalid_o,
    input  logic                        noc_arready_i,

    // NoC Interface - Write Channel
    output logic [DATA_WIDTH-1:0]       noc_wdata_o,
    output logic [DATA_WIDTH/8-1:0]     noc_wstrb_o,
    output logic                        noc_wvalid_o,
    input  logic                        noc_wready_i,
    output logic [ID_WIDTH-1:0]         noc_awid_o,
    output logic [ADDR_WIDTH-1:0]       noc_awaddr_o,
    output logic                        noc_awvalid_o,
    input  logic                        noc_awready_i,
    input  logic                        noc_bvalid_i,
    input  logic [ID_WIDTH-1:0]         noc_bid_i,

    // Control Interface
    input  logic [31:0]                 cfg_base_addr_i,
    input  logic [31:0]                 cfg_ctrl_i,
    output logic [31:0]                 cfg_status_o,
    output logic                        intr_compute_done_o,
    output logic                        intr_error_o,
    output logic                        intr_watchdog_o,

    // Memory Interface - Weight SRAM
    output logic                        weight_sram_clk_o,
    output logic                        weight_sram_csb_o,
    output logic [15:0]                 weight_sram_addr_o,
    output logic [511:0]                weight_sram_wdata_o,
    output logic [63:0]                 weight_sram_wmask_o,
    input  logic [511:0]                weight_sram_rdata_i,

    // Memory Interface - Activation SRAM
    output logic                        act_sram_clk_o,
    output logic                        act_sram_csb_o,
    output logic [15:0]                 act_sram_addr_o,
    output logic [511:0]                act_sram_wdata_o,
    output logic [63:0]                 act_sram_wmask_o,
    input  logic [511:0]                act_sram_rdata_i,

    // Memory Interface - Output Buffer
    output logic                        out_sram_clk_o,
    output logic                        out_sram_csb_o,
    output logic [14:0]                 out_sram_addr_o,
    output logic [511:0]                out_sram_wdata_o,
    output logic [63:0]                 out_sram_wmask_o,
    input  logic [511:0]                out_sram_rdata_i
);

    //-------------------------------------------------------------------------
    // Parameters
    //-------------------------------------------------------------------------
    localparam int NUM_WEIGHT_BANKS     = 16;
    localparam int NUM_ACT_BANKS        = 16;
    localparam int NUM_OUT_BANKS        = 8;
    localparam int BANK_WIDTH           = 512;
    localparam int BANK_DEPTH           = 131072; // 128KB per bank

    //-------------------------------------------------------------------------
    // Signals
    //-------------------------------------------------------------------------
    // Control signals
    logic                               ctrl_enable;
    logic                               ctrl_reset;
    logic [3:0]                         ctrl_op_type;
    logic [15:0]                        ctrl_dim_n;
    logic [15:0]                        ctrl_dim_h;
    logic [15:0]                        ctrl_dim_w;
    logic [15:0]                        ctrl_dim_k;
    logic [15:0]                        ctrl_dim_c;
    logic [15:0]                        ctrl_stride_h;
    logic [15:0]                        ctrl_stride_w;
    logic [15:0]                        ctrl_pad_h;
    logic [15:0]                        ctrl_pad_w;
    logic                               ctrl_start;

    // Status signals
    logic                               status_busy;
    logic                               status_done;
    logic [7:0]                         status_error;

    // Data path signals
    logic [511:0]                       weight_data [NUM_WEIGHT_BANKS-1:0];
    logic [511:0]                       act_data [NUM_ACT_BANKS-1:0];
    logic [511:0]                       out_data [NUM_OUT_BANKS-1:0];

    // DMA signals
    logic                               dma_req;
    logic [31:0]                        dma_src_addr;
    logic [31:0]                        dma_dst_addr;
    logic [21:0]                        dma_size;
    logic [2:0]                         dma_op;
    logic                               dma_done;
    logic                               dma_error;

    //-------------------------------------------------------------------------
    // Control Unit
    //-------------------------------------------------------------------------
    npu_cluster_ctrl u_ctrl (
        .clk_i                  (clk_i),
        .rst_ni                 (rst_ni),
        .cfg_base_addr_i        (cfg_base_addr_i),
        .cfg_ctrl_i             (cfg_ctrl_i),
        .cfg_status_o           (cfg_status_o),
        .ctrl_enable_o          (ctrl_enable),
        .ctrl_reset_o           (ctrl_reset),
        .ctrl_op_type_o         (ctrl_op_type),
        .ctrl_dim_n_o           (ctrl_dim_n),
        .ctrl_dim_h_o           (ctrl_dim_h),
        .ctrl_dim_w_o           (ctrl_dim_w),
        .ctrl_dim_k_o           (ctrl_dim_k),
        .ctrl_dim_c_o           (ctrl_dim_c),
        .ctrl_stride_h_o        (ctrl_stride_h),
        .ctrl_stride_w_o        (ctrl_stride_w),
        .ctrl_pad_h_o           (ctrl_pad_h),
        .ctrl_pad_w_o           (ctrl_pad_w),
        .ctrl_start_o           (ctrl_start),
        .status_busy_i          (status_busy),
        .status_done_i          (status_done),
        .status_error_i         (status_error),
        .intr_compute_done_o    (intr_compute_done_o),
        .intr_error_o           (intr_error_o),
        .intr_watchdog_o        (intr_watchdog_o)
    );

    //-------------------------------------------------------------------------
    // NPU Core
    //-------------------------------------------------------------------------
    npu_core #(
        .DATA_WIDTH             (DATA_WIDTH)
    ) u_core (
        .clk_i                  (clk_i),
        .rst_ni                 (rst_ni),
        .enable_i               (ctrl_enable),
        .op_type_i              (ctrl_op_type),
        .dim_n_i                (ctrl_dim_n),
        .dim_h_i                (ctrl_dim_h),
        .dim_w_i                (ctrl_dim_w),
        .dim_k_i                (ctrl_dim_k),
        .dim_c_i                (ctrl_dim_c),
        .stride_h_i             (ctrl_stride_h),
        .stride_w_i             (ctrl_stride_w),
        .pad_h_i                (ctrl_pad_h),
        .pad_w_i                (ctrl_pad_w),
        .start_i                (ctrl_start),
        .weight_data_i          (weight_data),
        .act_data_i             (act_data),
        .out_data_o             (out_data),
        .weight_sram_clk_o      (weight_sram_clk_o),
        .weight_sram_csb_o      (weight_sram_csb_o),
        .weight_sram_addr_o     (weight_sram_addr_o),
        .weight_sram_wdata_o    (weight_sram_wdata_o),
        .weight_sram_wmask_o    (weight_sram_wmask_o),
        .weight_sram_rdata_i    (weight_sram_rdata_i),
        .act_sram_clk_o         (act_sram_clk_o),
        .act_sram_csb_o         (act_sram_csb_o),
        .act_sram_addr_o        (act_sram_addr_o),
        .act_sram_wdata_o       (act_sram_wdata_o),
        .act_sram_wmask_o       (act_sram_wmask_o),
        .act_sram_rdata_i       (act_sram_rdata_i),
        .out_sram_clk_o         (out_sram_clk_o),
        .out_sram_csb_o         (out_sram_csb_o),
        .out_sram_addr_o        (out_sram_addr_o),
        .out_sram_wdata_o       (out_sram_wdata_o),
        .out_sram_wmask_o       (out_sram_wmask_o),
        .out_sram_rdata_i       (out_sram_rdata_i),
        .busy_o                 (status_busy),
        .done_o                 (status_done),
        .error_o                (status_error)
    );

    //-------------------------------------------------------------------------
    // DMA Engine
    //-------------------------------------------------------------------------
    dma_engine #(
        .ID_WIDTH               (ID_WIDTH),
        .ADDR_WIDTH             (ADDR_WIDTH),
        .DATA_WIDTH             (DATA_WIDTH)
    ) u_dma (
        .clk_i                  (clk_i),
        .rst_ni                 (rst_ni),
        .noc_rdata_i            (noc_rdata_i),
        .noc_rvalid_i           (noc_rvalid_i),
        .noc_rid_o              (noc_rid_o),
        .noc_araddr_o           (noc_araddr_o),
        .noc_arvalid_o          (noc_arvalid_o),
        .noc_arready_i          (noc_arready_i),
        .noc_wdata_o            (noc_wdata_o),
        .noc_wstrb_o            (noc_wstrb_o),
        .noc_wvalid_o           (noc_wvalid_o),
        .noc_wready_i           (noc_wready_i),
        .noc_awid_o             (noc_awid_o),
        .noc_awaddr_o           (noc_awaddr_o),
        .noc_awvalid_o          (noc_awvalid_o),
        .noc_awready_i          (noc_awready_i),
        .noc_bvalid_i           (noc_bvalid_i),
        .noc_bid_i              (noc_bid_i),
        .req_i                  (dma_req),
        .src_addr_i             (dma_src_addr),
        .dst_addr_i             (dma_dst_addr),
        .size_i                 (dma_size),
        .op_i                   (dma_op),
        .done_o                 (dma_done),
        .error_o                (dma_error)
    );

    //-------------------------------------------------------------------------
    // Weight SRAM Banks
    //-------------------------------------------------------------------------
    generate
        for (genvar i = 0; i < NUM_WEIGHT_BANKS; i++) begin : GEN_WEIGHT_BANKS
            assign weight_data[i] = weight_sram_rdata_i;
        end
    endgenerate

    //-------------------------------------------------------------------------
    // Activation SRAM Banks
    //-------------------------------------------------------------------------
    generate
        for (genvar i = 0; i < NUM_ACT_BANKS; i++) begin : GEN_ACT_BANKS
            assign act_data[i] = act_sram_rdata_i;
        end
    endgenerate

    //-------------------------------------------------------------------------
    // Output Buffer Banks
    //-------------------------------------------------------------------------
    generate
        for (genvar i = 0; i < NUM_OUT_BANKS; i++) begin : GEN_OUT_BANKS
            assign out_data[i] = out_sram_rdata_i;
        end
    endgenerate

endmodule
