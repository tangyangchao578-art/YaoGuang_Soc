// ============================================================================
// Module: soc_clock_reset
// Description: YaoGuang SoC 时钟复位树
// Author: YaoGuang RTL Team
// Version: V1.0
// Date: 2026-01-18
// ============================================================================

`timescale 1ns / 1ps

module soc_clock_reset (
    // ============================================================================
    // 外部时钟复位接口
    // ============================================================================
    
    input  logic                         osc_24mhz,        // 24 MHz 主晶振
    input  logic                         osc_32k,          // 32.768 kHz RTC 晶振
    input  logic                         por_n,            // 上电复位 (低有效)
    input  logic                         ext_rst_n,        // 外部复位 (低有效)
    
    // ============================================================================
    // 时钟输出
    // ============================================================================
    
    output logic                         clk_core,         // CPU 时钟 1.5-2.0 GHz
    output logic                         clk_safety,       // 安全岛时钟 1.0-1.5 GHz
    output logic                         clk_npu,          // NPU 时钟 1.5-2.0 GHz
    output logic                         clk_gpu,          // GPU 时钟 1.0-1.5 GHz
    output logic                         clk_isp,          // ISP 时钟 800 MHz
    output logic                         clk_noc,          // NoC 时钟 2.0 GHz
    output logic                         clk_mem,          // DDR 时钟 1.6 GHz
    output logic                         clk_sys,          // 系统时钟 500 MHz
    output logic                         clk_usb,          // USB 时钟 480 MHz
    output logic                         clk_pcie,         // PCIe 时钟 250 MHz
    output logic                         clk_eth,          // Ethernet 时钟 312.5 MHz
    output logic                         clk_rtc,          // RTC 时钟 32.768 kHz
    
    // ============================================================================
    // 复位输出
    // ============================================================================
    
    output logic                         rst_core_n,       // CPU 复位
    output logic                         rst_safety_n,     // 安全岛复位
    output logic                         rst_npu_n,        // NPU 复位
    output logic                         rst_gpu_n,        // GPU 复位
    output logic                         rst_isp_n,        // ISP 复位
    output logic                         rst_noc_n,        // NoC 复位
    output logic                         rst_mem_n,        // DDR 复位
    output logic                         rst_sys_n,        // 系统复位
    output logic                         rst_pcie_n,       // PCIe 复位
    output logic                         rst_usb_n,        // USB 复位
    output logic                         rst_eth_n,        // Ethernet 复位
    output logic                         rst_rtc_n,        // RTC 复位
    
    // ============================================================================
    // PLL 状态
    // ============================================================================
    
    output logic                         pll_main_lock,
    output logic                         pll_ddr_lock,
    output logic                         pll_peri_lock,
    output logic                         pll_usb_lock,
    output logic                         pll_pcie_lock,
    output logic                         pll_eth_lock,
    
    // ============================================================================
    // 时钟门控控制
    // ============================================================================
    
    input  logic                         cg_cpu_en,
    input  logic                         cg_npu_en,
    input  logic                         cg_gpu_en,
    input  logic                         cg_isp_en,
    input  logic                         cg_sys_en,
    
    // ============================================================================
    // PMU 接口
    // ============================================================================
    
    input  logic [11:0]                  pwr_domain_on,    // 电源域开关
    input  logic                         global_reset,     // 全局复位
    output logic [11:0]                  reset_status,     // 复位状态
    output logic                         watchdog_timeout, // 看门狗超时
    
    // ============================================================================
    // 状态与状态
    // ============================================================================
    
    output logic                         init_done         // 初始化完成
);
    
    // ============================================================================
    // 内部信号
    // ============================================================================
    
    logic                                clk_24mhz_buf;
    logic                                clk_32k_buf;
    logic                                pll_main_clk;
    logic                                pll_ddr_clk;
    logic                                pll_peri_clk;
    logic                                pll_usb_clk;
    logic                                pll_pcie_clk;
    logic                                pll_eth_clk;
    
    logic                                rst_por_sync;
    logic                                rst_main_sync;
    logic                                rst_global_sync;
    
    logic                                por_release;
    logic [15:0]                         por_counter;
    logic                                watchdog_counter_enable;
    logic [31:0]                         watchdog_counter;
    
    // ============================================================================
    // 时钟缓冲器实例化
    // ============================================================================
    
    // 24 MHz 主时钟缓冲
    clk_buffer #(
        .NUM_GATES        (1)
    ) clk_buf_24mhz (
        .clk_in           (osc_24mhz),
        .clk_out          (clk_24mhz_buf)
    );
    
    // 32.768 kHz RTC 时钟缓冲
    clk_buffer #(
        .NUM_GATES        (1)
    ) clk_buf_32k (
        .clk_in           (osc_32k),
        .clk_out          (clk_rtc)
    );
    
    // ============================================================================
    // PLL 实例化
    // ============================================================================
    
    // 主 PLL (CPU/NPU/GPU/ISP/NoC)
    pll_main #(
        .REF_FREQ         (24.0),
        .OUT_FREQ_CORE    (2000.0),  // 2.0 GHz
        .OUT_FREQ_NPU     (2000.0),  // 2.0 GHz
        .OUT_FREQ_GPU     (1500.0),  // 1.5 GHz
        .OUT_FREQ_ISP     (800.0),   // 800 MHz
        .OUT_FREQ_NOC     (2000.0)   // 2.0 GHz
    ) pll_main_inst (
        .ref_clk          (clk_24mhz_buf),
        .rst_n            (rst_por_sync),
        .lock             (pll_main_lock),
        .clk_core         (pll_main_clk),
        .clk_npu          (clk_npu),
        .clk_gpu          (clk_gpu),
        .clk_isp          (clk_isp),
        .clk_noc          (clk_noc)
    );
    
    // DDR PLL
    pll_ddr #(
        .REF_FREQ         (24.0),
        .OUT_FREQ         (1600.0)   // 1.6 GHz
    ) pll_ddr_inst (
        .ref_clk          (clk_24mhz_buf),
        .rst_n            (rst_por_sync),
        .lock             (pll_ddr_lock),
        .clk_mem          (clk_mem)
    );
    
    // 外设 PLL
    pll_peri #(
        .REF_FREQ         (24.0),
        .OUT_FREQ_SYS     (500.0),   // 500 MHz
        .OUT_FREQ_ETH     (312.5)    // 312.5 MHz
    ) pll_peri_inst (
        .ref_clk          (clk_24mhz_buf),
        .rst_n            (rst_por_sync),
        .lock             (pll_peri_lock),
        .clk_sys          (clk_sys),
        .clk_eth          (clk_eth)
    );
    
    // USB PLL
    pll_usb #(
        .REF_FREQ         (24.0),
        .OUT_FREQ         (480.0)    // 480 MHz
    ) pll_usb_inst (
        .ref_clk          (clk_24mhz_buf),
        .rst_n            (rst_por_sync),
        .lock             (pll_usb_lock),
        .clk_usb          (clk_usb)
    );
    
    // PCIe PLL
    pll_pcie #(
        .REF_FREQ         (24.0),
        .OUT_FREQ         (250.0)    // 250 MHz
    ) pll_pcie_inst (
        .ref_clk          (clk_24mhz_buf),
        .rst_n            (rst_por_sync),
        .lock             (pll_pcie_lock),
        .clk_pcie         (clk_pcie)
    );
    
    // ============================================================================
    // 时钟门控实例化
    // ============================================================================
    
    // CPU 时钟门控
    clk_gate clk_gate_cpu (
        .clk_in           (clk_noc),
        .clk_en           (cg_cpu_en),
        .clk_out          (clk_core)
    );
    
    // NPU 时钟门控
    clk_gate clk_gate_npu (
        .clk_in           (clk_npu),
        .clk_en           (cg_npu_en),
        .clk_out          (clk_npu)
    );
    
    // GPU 时钟门控
    clk_gate clk_gate_gpu (
        .clk_in           (clk_gpu),
        .clk_en           (cg_gpu_en),
        .clk_out          (clk_gpu)
    );
    
    // ISP 时钟门控
    clk_gate clk_gate_isp (
        .clk_in           (clk_isp),
        .clk_en           (cg_isp_en),
        .clk_out          (clk_isp)
    );
    
    // 系统时钟门控
    clk_gate clk_gate_sys (
        .clk_in           (clk_sys),
        .clk_en           (cg_sys_en),
        .clk_out          (clk_sys)
    );
    
    // ============================================================================
    // 复位同步与生成
    // ============================================================================
    
    // POR 复位同步
    rst_sync rst_sync_por (
        .clk              (clk_24mhz_buf),
        .rst_in           (por_n),
        .rst_out          (rst_por_sync)
    );
    
    // 外部复位同步
    rst_sync rst_sync_ext (
        .clk              (clk_24mhz_buf),
        .rst_in           (ext_rst_n),
        .rst_out          (rst_main_sync)
    );
    
    // 全局复位同步
    rst_sync rst_sync_global (
        .clk              (clk_24mhz_buf),
        .rst_in           (global_reset),
        .rst_out          (rst_global_sync)
    );
    
    // POR 释放计数器
    always_ff @(posedge clk_24mhz_buf or negedge rst_por_sync) begin
        if (!rst_por_sync) begin
            por_counter <= 16'h0000;
        end else begin
            if (!por_release) begin
                por_counter <= por_counter + 1;
            end
        end
    end
    
    assign por_release = (por_counter == 16'hFFFF);
    assign init_done = por_release & pll_main_lock & pll_ddr_lock;
    
    // ============================================================================
    // 复位生成逻辑
    // ============================================================================
    
    // 系统复位生成
    assign rst_core_n   = rst_por_sync & rst_main_sync & rst_global_sync;
    assign rst_safety_n = rst_por_sync & rst_main_sync & rst_global_sync;
    assign rst_npu_n    = rst_por_sync & rst_main_sync & rst_global_sync;
    assign rst_gpu_n    = rst_por_sync & rst_main_sync & rst_global_sync;
    assign rst_isp_n    = rst_por_sync & rst_main_sync & rst_global_sync;
    assign rst_noc_n    = rst_por_sync & rst_main_sync & rst_global_sync;
    assign rst_mem_n    = rst_por_sync & rst_main_sync & rst_global_sync;
    assign rst_sys_n    = rst_por_sync & rst_main_sync & rst_global_sync;
    assign rst_pcie_n   = rst_por_sync & rst_main_sync & rst_global_sync;
    assign rst_usb_n    = rst_por_sync & rst_main_sync & rst_global_sync;
    assign rst_eth_n    = rst_por_sync & rst_main_sync & rst_global_sync;
    assign rst_rtc_n    = rst_por_sync;
    
    // 复位状态寄存器
    always_ff @(posedge clk_24mhz_buf) begin
        reset_status[0]  <= ~rst_core_n;
        reset_status[1]  <= ~rst_safety_n;
        reset_status[2]  <= ~rst_npu_n;
        reset_status[3]  <= ~rst_gpu_n;
        reset_status[4]  <= ~rst_isp_n;
        reset_status[5]  <= ~rst_noc_n;
        reset_status[6]  <= ~rst_mem_n;
        reset_status[7]  <= ~rst_sys_n;
        reset_status[8]  <= ~rst_pcie_n;
        reset_status[9]  <= ~rst_usb_n;
        reset_status[10] <= ~rst_eth_n;
        reset_status[11] <= ~rst_rtc_n;
    end
    
    // ============================================================================
    // 看门狗定时器
    // ============================================================================
    
    always_ff @(posedge clk_24mhz_buf or negedge rst_por_sync) begin
        if (!rst_por_sync) begin
            watchdog_counter <= 32'h0000_0000;
            watchdog_timeout <= 1'b0;
        end else begin
            if (watchdog_counter_enable) begin
                watchdog_counter <= watchdog_counter + 1;
                if (watchdog_counter == 32'hFFFF_FFFF) begin
                    watchdog_timeout <= 1'b1;
                end
            end else begin
                watchdog_counter <= 32'h0000_0000;
                watchdog_timeout <= 1'b0;
            end
        end
    end
    
    // 时钟使能控制
    assign watchdog_counter_enable = 1'b1;  // 始终使能看门狗
    
endmodule
