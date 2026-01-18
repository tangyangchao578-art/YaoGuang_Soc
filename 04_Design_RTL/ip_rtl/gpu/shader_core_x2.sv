//==============================================================================
//  Shader Core Cluster x2 - YaoGuang SoC
//==============================================================================
//  File: shader_core_x2.sv
//  Description: 双渲染核心集群模块
//==============================================================================

`timescale 1ns/100ps

module shader_core_x2 #(
    parameter int EU_COUNT = 32,
    parameter int FP32_OPS_PER_CYCLE = 2,
    parameter int INT32_OPS_PER_CYCLE = 2,
    parameter int FP16_OPS_PER_CYCLE = 4,
    parameter int INT8_OPS_PER_CYCLE = 8,
    parameter int AXI_DATA_WIDTH = 256,
    parameter int LOCAL_MEM_SIZE = 65536,  // 64KB
    parameter int UNIFORM_CACHE_SIZE = 32768,  // 32KB
    parameter int TEXTURE_CACHE_SIZE = 65536,  // 64KB
    parameter int LOAD_STORE_CACHE_SIZE = 32768  // 32KB
) (
    //============= 时钟复位 =============
    input  logic                        clk_i,
    input  logic                        rst_n_i,
    input  logic                        enable_i,

    //============= 状态接口 =============
    output logic                        busy_o,
    output logic [31:0]                 perf_counter_o,

    //============= 作业接口 =============
    input  logic [31:0]                 job_addr_i,
    input  logic                        job_valid_i,
    output logic                        job_done_o,

    //============= L2 Cache 接口 =============
    output logic [AXI_DATA_WIDTH-1:0]   l2_raddr_o,
    output logic [AXI_DATA_WIDTH-1:0]   l2_wdata_o,
    output logic [AXI_DATA_WIDTH-1:0]   l2_addr_o,
    output logic                        l2_read_o,
    output logic                        l2_write_o,
    input  logic                        l2_ready_i,
    input  logic [AXI_DATA_WIDTH-1:0]   l2_rdata_i
);

    //============= 内部信号 =============
    logic                                cluster0_enable;
    logic                                cluster1_enable;
    logic                                cluster0_busy;
    logic                                cluster1_busy;
    logic [31:0]                         cluster0_job_addr;
    logic [31:0]                         cluster1_job_addr;
    logic                                cluster0_job_valid;
    logic                                cluster1_job_valid;
    logic                                cluster0_job_done;
    logic                                cluster1_job_done;

    logic [31:0]                         job_counter;
    logic [63:0]                         cycle_counter;

    //============================================================================
    //  作业调度器
    //============================================================================
    job_scheduler #(
        .NUM_CLUSTERS(2)
    ) u_job_scheduler (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .enable_i(enable_i),
        .global_job_addr_i(job_addr_i),
        .global_job_valid_i(job_valid_i),
        .global_job_done_o(job_done_o),
        .cluster_enable_o({cluster1_enable, cluster0_enable}),
        .cluster_busy_i({cluster1_busy, cluster0_busy}),
        .cluster_job_addr_o({cluster1_job_addr, cluster0_job_addr}),
        .cluster_job_valid_o({cluster1_job_valid, cluster0_job_valid}),
        .cluster_job_done_i({cluster1_job_done, cluster0_job_done}),
        .job_counter_o(job_counter)
    );

    //============================================================================
    //  Shader Core Cluster 0
    //============================================================================
    shader_core_cluster #(
        .EU_COUNT(EU_COUNT),
        .FP32_OPS_PER_CYCLE(FP32_OPS_PER_CYCLE),
        .INT32_OPS_PER_CYCLE(INT32_OPS_PER_CYCLE),
        .FP16_OPS_PER_CYCLE(FP16_OPS_PER_CYCLE),
        .INT8_OPS_PER_CYCLE(INT8_OPS_PER_CYCLE),
        .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
        .LOCAL_MEM_SIZE(LOCAL_MEM_SIZE),
        .UNIFORM_CACHE_SIZE(UNIFORM_CACHE_SIZE),
        .TEXTURE_CACHE_SIZE(TEXTURE_CACHE_SIZE),
        .LOAD_STORE_CACHE_SIZE(LOAD_STORE_CACHE_SIZE)
    ) u_cluster0 (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .enable_i(cluster0_enable),
        .busy_o(cluster0_busy),
        .job_addr_i(cluster0_job_addr),
        .job_valid_i(cluster0_job_valid),
        .job_done_o(cluster0_job_done),
        .l2_raddr_o(l2_raddr_o),
        .l2_wdata_o(l2_wdata_o),
        .l2_addr_o(l2_addr_o),
        .l2_read_o(l2_read_o),
        .l2_write_o(l2_write_o),
        .l2_ready_i(l2_ready_i),
        .l2_rdata_i(l2_rdata_i)
    );

    //============================================================================
    //  Shader Core Cluster 1
    //============================================================================
    shader_core_cluster #(
        .EU_COUNT(EU_COUNT),
        .FP32_OPS_PER_CYCLE(FP32_OPS_PER_CYCLE),
        .INT32_OPS_PER_CYCLE(INT32_OPS_PER_CYCLE),
        .FP16_OPS_PER_CYCLE(FP16_OPS_PER_CYCLE),
        .INT8_OPS_PER_CYCLE(INT8_OPS_PER_CYCLE),
        .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
        .LOCAL_MEM_SIZE(LOCAL_MEM_SIZE),
        .UNIFORM_CACHE_SIZE(UNIFORM_CACHE_SIZE),
        .TEXTURE_CACHE_SIZE(TEXTURE_CACHE_SIZE),
        .LOAD_STORE_CACHE_SIZE(LOAD_STORE_CACHE_SIZE)
    ) u_cluster1 (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .enable_i(cluster1_enable),
        .busy_o(cluster1_busy),
        .job_addr_i(cluster1_job_addr),
        .job_valid_i(cluster1_job_valid),
        .job_done_o(cluster1_job_done),
        .l2_raddr_o(),
        .l2_wdata_o(),
        .l2_addr_o(),
        .l2_read_o(),
        .l2_write_o(),
        .l2_ready_i(l2_ready_i),
        .l2_rdata_i(l2_rdata_i)
    );

    //============================================================================
    //  忙碌状态合并
    //============================================================================
    assign busy_o = cluster0_busy | cluster1_busy;

    //============================================================================
    //  性能计数器
    //============================================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            cycle_counter <= '0;
            perf_counter_o <= '0;
        end else begin
            cycle_counter <= cycle_counter + 1;
            if (enable_i && busy_o) begin
                perf_counter_o <= cycle_counter[31:0];
            end
        end
    end

endmodule
