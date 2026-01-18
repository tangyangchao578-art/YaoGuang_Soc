//==============================================================================
//  GPU Top Module - YaoGuang SoC
//==============================================================================
//  File: gpu_top.sv
//  Description: GPU顶层集成模块
//==============================================================================

`timescale 1ns/100ps

module gpu_top #(
    parameter int NUM_CLUSTERS = 2,
    parameter int EU_PER_CLUSTER = 32,
    parameter int L2_CACHE_SIZE = 2048,  // 2MB in KB
    parameter int AXI_DATA_WIDTH = 256,
    parameter int AXI_ADDR_WIDTH = 40
) (
    //============= 时钟复位 =============
    input  logic                        clk_i,
    input  logic                        rst_n_i,
    input  logic                        clk_gating_gpuclk_o,

    //============= ACE4 系统接口 =============
    output logic [AXI_ADDR_WIDTH-1:0]   ace_awaddr_o,
    output logic [3:0]                  ace_awid_o,
    output logic [7:0]                  ace_awlen_o,
    output logic [2:0]                  awsize_o,
    output logic [1:0]                  awburst_o,
    output logic                        awvalid_o,
    input  logic                        awready_i,
    output logic [AXI_DATA_WIDTH-1:0]   wdata_o,
    output logic [AXI_DATA_WIDTH/8-1:0] wstrb_o,
    output logic                        wlast_o,
    output logic                        wvalid_o,
    input  logic                        wready_i,
    input  logic [3:0]                  bid_i,
    input  logic [1:0]                  bresp_i,
    input  logic                        bvalid_i,
    output logic                        bready_o,
    output logic [AXI_ADDR_WIDTH-1:0]   araddr_o,
    output logic [3:0]                  arid_o,
    output logic [7:0]                  arlen_o,
    output logic [2:0]                  arsize_o,
    output logic [1:0]                  arburst_o,
    output logic                        arvalid_o,
    input  logic                        arready_i,
    input  logic [AXI_DATA_WIDTH-1:0]   rdata_i,
    input  logic [3:0]                  rid_i,
    input  logic                        rlast_i,
    input  logic [1:0]                  rresp_i,
    input  logic                        rvalid_i,
    output logic                        rready_o,

    //============= ACE 一致性信号 =============
    output logic [3:0]                  ace_awdomain_o,
    output logic [3:0]                  ace_awuser_o,
    output logic                        ace_awunique_o,
    output logic [3:0]                  ace_ardomain_o,
    output logic [3:0]                  ace_aruser_o,
    output logic                        ace_arunique_o,
    input  logic [3:0]                  ace_crresp_i,
    input  logic [3:0]                  ace_drresp_i,

    //============= 中断接口 =============
    output logic                        irq_job_complete_o,
    output logic                        irq_gpu_fault_o,
    output logic                        irq_context_fault_o,

    //============= 配置接口 =============
    input  logic [31:0]                 reg_addr_i,
    input  logic [31:0]                 reg_wdata_i,
    input  logic                        reg_write_i,
    input  logic                        reg_read_i,
    output logic [31:0]                 reg_rdata_o,
    output logic                        reg_ready_o,

    //============= 状态信号 =============
    output logic [31:0]                 perf_cycle_cnt_o,
    output logic [31:0]                 perf_job_cnt_o
);

    //============= 内部信号 =============
    logic                                cmd_valid;
    logic                                cmd_ready;
    logic [31:0]                         cmd_base_addr;
    logic [31:0]                         cmd_size;
    logic [3:0]                          cmd_job_type;

    logic                                job_complete_int;
    logic                                gpu_fault_int;
    logic                                context_fault_int;

    //============= L2 Cache 接口 =============
    logic                                l2_enable;
    logic [AXI_ADDR_WIDTH-1:0]           l2_raddr;
    logic [AXI_DATA_WIDTH-1:0]           l2_wdata;
    logic [AXI_ADDR_WIDTH-1:0]           l2_addr;
    logic                                l2_read;
    logic                                l2_write;
    logic                                l2_ready;
    logic [AXI_DATA_WIDTH-1:0]           l2_rdata;

    //============= Shader Core 接口 =============
    logic [NUM_CLUSTERS-1:0]             core_enable;
    logic [NUM_CLUSTERS-1:0]             core_busy;
    logic [31:0]                         core_job_addr [NUM_CLUSTERS];
    logic [NUM_CLUSTERS-1:0]             core_job_valid;
    logic [NUM_CLUSTERS-1:0]             core_job_done;

    //============= Tiler 接口 =============
    logic                                tiler_enable;
    logic                                tiler_busy;
    logic [31:0]                         tiler_tile_size;
    logic [31:0]                         tiler_base_addr;

    //============================================================================
    //  Command Processor
    //============================================================================
    command_processor #(
        .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH)
    ) u_command_processor (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .reg_addr_i(reg_addr_i),
        .reg_wdata_i(reg_wdata_i),
        .reg_write_i(reg_write_i),
        .reg_read_i(reg_read_i),
        .reg_rdata_o(reg_rdata_o),
        .reg_ready_o(reg_ready_o),
        .cmd_valid_o(cmd_valid),
        .cmd_ready_i(cmd_ready),
        .cmd_base_addr_o(cmd_base_addr),
        .cmd_size_o(cmd_size),
        .cmd_job_type_o(cmd_job_type),
        .job_complete_i(job_complete_int),
        .gpu_fault_i(gpu_fault_int),
        .context_fault_i(context_fault_int),
        .irq_job_complete_o(irq_job_complete_o),
        .irq_gpu_fault_o(irq_gpu_fault_o),
        .irq_context_fault_o(irq_context_fault_o),
        .perf_cycle_cnt_o(perf_cycle_cnt_o),
        .perf_job_cnt_o(perf_job_cnt_o)
    );

    //============================================================================
    //  L2 Cache
    //============================================================================
    l2_cache_controller #(
        .CACHE_SIZE(L2_CACHE_SIZE),
        .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
        .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH)
    ) u_l2_cache (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .enable_i(l2_enable),
        .raddr_i(l2_raddr),
        .waddr_i(l2_addr),
        .wdata_i(l2_wdata),
        .read_i(l2_read),
        .write_i(l2_write),
        .ready_o(l2_ready),
        .rdata_o(l2_rdata),
        .axi_awaddr_o(ace_awaddr_o),
        .axi_awid_o(ace_awid_o),
        .axi_awlen_o(ace_awlen_o),
        .awsize_o(awsize_o),
        .awburst_o(awburst_o),
        .awvalid_o(awvalid_o),
        .awready_i(awready_i),
        .wdata_o(wdata_o),
        .wstrb_o(wstrb_o),
        .wlast_o(wlast_o),
        .wvalid_o(wvalid_o),
        .wready_i(wready_i),
        .bid_i(bid_i),
        .bresp_i(bresp_i),
        .bvalid_i(bvalid_i),
        .bready_o(bready_o),
        .araddr_o(araddr_o),
        .arid_o(arid_o),
        .arlen_o(arlen_o),
        .arsize_o(arsize_o),
        .arburst_o(arburst_o),
        .arvalid_o(arvalid_o),
        .arready_i(arready_i),
        .rdata_i(rdata_i),
        .rid_i(rid_i),
        .rlast_i(rlast_i),
        .rresp_i(rresp_i),
        .rvalid_i(rvalid_i),
        .rready_o(rready_o)
    );

    //============================================================================
    //  Shader Core Cluster x2
    //============================================================================
    generate
        for (genvar i = 0; i < NUM_CLUSTERS; i++) begin : gen_shader_core
            shader_core_cluster #(
                .EU_COUNT(EU_PER_CLUSTER),
                .AXI_DATA_WIDTH(AXI_DATA_WIDTH)
            ) u_shader_core (
                .clk_i(clk_i),
                .rst_n_i(rst_n_i),
                .enable_i(core_enable[i]),
                .busy_o(core_busy[i]),
                .job_addr_i(core_job_addr[i]),
                .job_valid_i(core_job_valid[i]),
                .job_done_o(core_job_done[i]),
                .l2_raddr_o(l2_raddr),
                .l2_wdata_o(l2_wdata),
                .l2_addr_o(l2_addr),
                .l2_read_o(l2_read),
                .l2_write_o(l2_write),
                .l2_ready_i(l2_ready),
                .l2_rdata_i(l2_rdata)
            );
        end
    endgenerate

    //============================================================================
    //  Tiler (Tile-Based Deferred Rendering)
    //============================================================================
    tiler_unit #(
        .MAX_TILE_WIDTH(32),
        .MAX_TILE_HEIGHT(32)
    ) u_tiler (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .enable_i(tiler_enable),
        .busy_o(tiler_busy),
        .tile_size_i(tiler_tile_size),
        .base_addr_i(tiler_base_addr),
        .core_busy_i(core_busy),
        .core_enable_o(core_enable),
        .core_job_addr_o(core_job_addr),
        .core_job_valid_o(core_job_valid),
        .core_job_done_i(core_job_done),
        .job_complete_o(job_complete_int),
        .gpu_fault_o(gpu_fault_int),
        .context_fault_o(context_fault_int)
    );

    //============================================================================
    //  时钟门控
    //============================================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            clk_gating_gpuclk_o <= 1'b1;
        end else begin
            if (cmd_valid && cmd_ready) begin
                clk_gating_gpuclk_o <= 1'b0;
            end else if (job_complete_int) begin
                clk_gating_gpuclk_o <= 1'b1;
            end
        end
    end

    //============================================================================
    //  断言与覆盖
    //============================================================================
    // FIFO 满检查
    `assert_no_overflow: assert property (
        @(posedge clk_i) !(cmd_valid && !cmd_ready)
    ) else $error("Command FIFO overflow");

endmodule
