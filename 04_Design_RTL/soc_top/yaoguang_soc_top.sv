// ============================================================================
// Module: yaoguang_soc_top
// Description: YaoGuang SoC 顶层模块
// Author: YaoGuang RTL Team
// Version: V1.0
// Date: 2026-03-01
// ============================================================================

`timescale 1ns / 1ps

module yaoguang_soc_top (
    // ============================================================================
    // 时钟和复位接口
    // ============================================================================
    
    // 主晶振输入
    input  logic                         osc_24mhz,        // 24 MHz 晶振
    
    // 外部复位输入
    input  logic                         por_n,              // 上电复位 (低有效)
    input  logic                         ext_rst_n,           // 外部复位 (低有效)
    
    // ============================================================================
    // 应用处理器接口 (8x Cortex-A78AE)
    // ============================================================================
    
    // ACE4 接口 - 8核集群
    input  logic                         cpu_a8_awvalid,
    input  logic                         cpu_a8_awready,
    input  logic [31:0]                cpu_a8_awaddr,
    input  logic [7:0]                  cpu_a8_awlen,
    input  logic [2:0]                  cpu_a8_awsize,
    input  logic [1:0]                  cpu_a8_awburst,
    input  logic [3:0]                  cpu_a8_awqos,
    
    input  logic                         cpu_a8_wvalid,
    input  logic                         cpu_a8_wready,
    input  logic [511:0]               cpu_a8_wdata,
    input  logic [63:0]                cpu_a8_wstrb,
    input  logic                         cpu_a8_wlast,
    
    input  logic                         cpu_a8_bvalid,
    input  logic                         cpu_a8_bready,
    input  logic [1:0]                  cpu_a8_bresp,
    
    input  logic                         cpu_a8_arvalid,
    input  logic                         cpu_a8_arready,
    input  logic [31:0]                cpu_a8_araddr,
    input  logic [7:0]                  cpu_a8_arlen,
    input  logic [2:0]                  cpu_a8_arsize,
    input  logic [1:0]                  cpu_a8_arburst,
    input  logic [3:0]                  cpu_a8_arqos,
    
    input  logic                         cpu_a8_rvalid,
    input  logic                         cpu_a8_rready,
    input  logic [511:0]               cpu_a8_rdata,
    input  logic [1:0]                  cpu_a8_rresp,
    input  logic                         cpu_a8_rlast,
    
    // CPU 中断输出
    output logic                         cpu_irq [7:0],
    
    // ============================================================================
    // 安全处理器接口 (2x Cortex-R52 锁步)
    // ============================================================================
    
    // AXI4 接口 - 安全岛
    input  logic                         cpu_safety_awvalid,
    input  logic                         cpu_safety_awready,
    input  logic [31:0]                cpu_safety_awaddr,
    input  logic [7:0]                  cpu_safety_awlen,
    input  logic [2:0]                  cpu_safety_awsize,
    input  logic [1:0]                  cpu_safety_awburst,
    
    input  logic                         cpu_safety_wvalid,
    input  logic                         cpu_safety_wready,
    input  logic [255:0]               cpu_safety_wdata,
    input  logic [31:0]                cpu_safety_wstrb,
    input  logic                         cpu_safety_wlast,
    
    input  logic                         cpu_safety_bvalid,
    input  logic                         cpu_safety_bready,
    input  logic [1:0]                  cpu_safety_bresp,
    
    input  logic                         cpu_safety_arvalid,
    input  logic                         cpu_safety_arready,
    input  logic [31:0]                cpu_safety_araddr,
    input  logic [7:0]                  cpu_safety_arlen,
    input  logic [2:0]                  cpu_safety_arsize,
    input  logic [1:0]                  cpu_safety_arburst,
    
    input  logic                         cpu_safety_rvalid,
    input  logic                         cpu_safety_rready,
    input  logic [255:0]               cpu_safety_rdata,
    input  logic [1:0]                  cpu_safety_rresp,
    
    // 安全中断输出
    output logic                         safety_irq [1:0],
    
    // 安全错误标志
    output logic                         safety_error,
    
    // ============================================================================
    // NPU 集群接口 (4x 集群)
    // ============================================================================
    
    // NPU Cluster 0
    input  logic                         npu0_awvalid,
    input  logic                         npu0_awready,
    input  logic [31:0]                npu0_awaddr,
    input  logic [7:0]                  npu0_awlen,
    input  logic [2:0]                  npu0_awsize,
    input  logic [1:0]                  npu0_awburst,
    
    input  logic                         npu0_wvalid,
    input  logic                         npu0_wready,
    input  logic [511:0]               npu0_wdata,
    input  logic [63:0]                npu0_wstrb,
    input  logic                         npu0_wlast,
    
    input  logic                         npu0_bvalid,
    input  logic                         npu0_bready,
    input  logic [1:0]                  npu0_bresp,
    
    input  logic                         npu0_arvalid,
    input  logic                         npu0_arready,
    input  logic [31:0]                npu0_araddr,
    input  logic [7:0]                  npu0_arlen,
    input  logic [2:0]                  npu0_arsize,
    input  logic [1:0]                  npu0_arburst,
    
    input  logic                         npu0_rvalid,
    input  logic                         npu0_rready,
    input  logic [511:0]               npu0_rdata,
    input  logic [1:0]                  npu0_rresp,
    input  logic                         npu0_rlast,
    
    output logic                         npu0_irq,
    output logic                         npu0_clk_en,
    
    // NPU Cluster 1, 2, 3 (同样接口)
    input  logic                         npu1_awvalid,
    input  logic                         npu1_awready,
    input  logic [31:0]                npu1_awaddr,
    input  logic [7:0]                  npu1_awlen,
    input  logic [2:0]                  npu1_awsize,
    input  logic [1:0]                  npu1_awburst,
    input  logic                         npu1_wvalid,
    input  logic                         npu1_wready,
    input  logic [511:0]               npu1_wdata,
    input  logic [63:0]                npu1_wstrb,
    input  logic                         npu1_wlast,
    input  logic                         npu1_bvalid,
    input  logic                         npu1_bready,
    input  logic [1:0]                  npu1_bresp,
    input  logic                         npu1_arvalid,
    input  logic                         npu1_arready,
    input  logic [31:0]                npu1_araddr,
    input  logic [7:0]                  npu1_arlen,
    input  logic [2:0]                  npu1_arsize,
    input  logic [1:0]                  npu1_arburst,
    input  logic                         npu1_rvalid,
    input  logic                         npu1_rready,
    input  logic [511:0]               npu1_rdata,
    input  logic [1:0]                  npu1_rresp,
    input  logic                         npu1_rlast,
    output logic                         npu1_irq,
    output logic                         npu1_clk_en,
    
    input  logic                         npu2_awvalid,
    input  logic                         npu2_awready,
    input  logic [31:0]                npu2_awaddr,
    input  logic [7:0]                  npu2_awlen,
    input  logic [2:0]                  npu2_awsize,
    input  logic [1:0]                  npu2_awburst,
    input  logic                         npu2_wvalid,
    input  logic                         npu2_wready,
    input  logic [511:0]               npu2_wdata,
    input  logic [63:0]                npu2_wstrb,
    input  logic                         npu2_wlast,
    input  logic                         npu2_bvalid,
    input  logic                         npu2_bready,
    input  logic [1:0]                  npu2_bresp,
    input  logic                         npu2_arvalid,
    input  logic                         npu2_arready,
    input  logic [31:0]                npu2_araddr,
    input  logic [7:0]                  npu2_arlen,
    input  logic [2:0]                  npu2_arsize,
    input  logic [1:0]                  npu2_arburst,
    input  logic                         npu2_rvalid,
    input  logic                         npu2_rready,
    input  logic [511:0]               npu2_rdata,
    input  logic [1:0]                  npu2_rresp,
    input  logic                         npu2_rlast,
    output logic                         npu2_irq,
    output logic                         npu2_clk_en,
    
    input  logic                         npu3_awvalid,
    input  logic                         npu3_awready,
    input  logic [31:0]                npu3_awaddr,
    input  logic [7:0]                  npu3_awlen,
    input  logic [2:0]                  npu3_awsize,
    input  logic [1:0]                  npu3_awburst,
    input  logic                         npu3_wvalid,
    input  logic                         npu3_wready,
    input  logic [511:0]               npu3_wdata,
    input  logic [63:0]                npu3_wstrb,
    input  logic                         npu3_wlast,
    input  logic                         npu3_bvalid,
    input  logic                         npu3_bready,
    input  logic [1:0]                  npu3_bresp,
    input  logic                         npu3_arvalid,
    input  logic                         npu3_arready,
    input  logic [31:0]                npu3_araddr,
    input  logic [7:0]                  npu3_arlen,
    input  logic [2:0]                  npu3_arsize,
    input  logic [1:0]                  npu3_arburst,
    input  logic                         npu3_rvalid,
    input  logic                         npu3_rready,
    input  logic [511:0]               npu3_rdata,
    input  logic [1:0]                  npu3_rresp,
    input  logic                         npu3_rlast,
    output logic                         npu3_irq,
    output logic                         npu3_clk_en,
    
    // ============================================================================
    // GPU 接口 (2x Mali-G78)
    // ============================================================================
    
    input  logic                         gpu_awvalid,
    input  logic                         gpu_awready,
    input  logic [31:0]                gpu_awaddr,
    input  logic [7:0]                  gpu_awlen,
    input  logic [2:0]                  gpu_awsize,
    input  logic [1:0]                  gpu_awburst,
    
    input  logic                         gpu_wvalid,
    input  logic                         gpu_wready,
    input  logic [511:0]               gpu_wdata,
    input  logic [63:0]                gpu_wstrb,
    input  logic                         gpu_wlast,
    
    input  logic                         gpu_bvalid,
    input  logic                         gpu_bready,
    input  logic [1:0]                  gpu_bresp,
    
    input  logic                         gpu_arvalid,
    input  logic                         gpu_arready,
    input  logic [31:0]                gpu_araddr,
    input  logic [7:0]                  gpu_arlen,
    input  logic [2:0]                  gpu_arsize,
    input  logic [1:0]                  gpu_arburst,
    
    input  logic                         gpu_rvalid,
    input  logic                         gpu_rready,
    input  logic [511:0]               gpu_rdata,
    input  logic [1:0]                  gpu_rresp,
    input  logic                         gpu_rlast,
    
    output logic                         gpu_irq,
    
    // ============================================================================
    // ISP 接口 (图像处理)
    // ============================================================================
    
    input  logic                         isp_awvalid,
    input  logic                         isp_awready,
    input  logic [31:0]                isp_awaddr,
    input  logic [7:0]                  isp_awlen,
    input  logic [2:0]                  isp_awsize,
    input  logic [1:0]                  isp_awburst,
    
    input  logic                         isp_wvalid,
    input  logic                         isp_wready,
    input  logic [255:0]               isp_wdata,
    input  logic [31:0]                isp_wstrb,
    input  logic                         isp_wlast,
    
    input  logic                         isp_bvalid,
    input  logic                         isp_bready,
    input  logic [1:0]                  isp_bresp,
    
    input  logic                         isp_arvalid,
    input  logic                         isp_arready,
    input  logic [31:0]                isp_araddr,
    input  logic [7:0]                  isp_arlen,
    input  logic [2:0]                  isp_arsize,
    input  logic [1:0]                  isp_arburst,
    
    input  logic                         isp_rvalid,
    input  logic                         isp_rready,
    input  logic [255:0]               isp_rdata,
    input  logic [1:0]                  isp_rresp,
    input  logic                         isp_rlast,
    
    // ============================================================================
    // 存储器接口 (LPDDR5)
    // ============================================================================
    
    input  logic                         ddr_phy_clk_p,
    input  logic                         ddr_phy_clk_n,
    input  logic                         ddr_phy_rst_n,
    
    // PHY 接口信号
    output logic [15:0]                ddr_dq,
    output logic [1:0]                 ddr_dqs_p,
    output logic [1:0]                 ddr_dqs_n,
    output logic [1:0]                 ddr_dm,
    output logic [1:0]                 ddr_dmi,
    
    output logic                         ddr_ca,
    output logic                         ddr_ra,
    output logic                         ddr_we_n,
    output logic [16:0]                ddr_cs_n,
    output logic [1:0]                 ddr_cke,
    output logic                         ddr_odt,
    
    output logic [7:0]                  ddr_bg,
    output logic [1:0]                 ddr_ba,
    output logic [2:0]                  ddr_act_n,
    output logic [15:0]                ddr_a,
    
    // ============================================================================
    // PCIe 接口 (PCIe Gen4 x8 + x4)
    // ============================================================================
    
    // PCIe x8 接口
    output logic                         pcie8_tx_p,
    output logic                         pcie8_tx_n,
    input  logic                         pcie8_rx_p,
    input  logic                         pcie8_rx_n,
    input  logic                         pcie8_refclk_p,
    input  logic                         pcie8_refclk_n,
    input  logic                         pcie8_perst_n,
    output logic                         pcie8_wake_n,
    
    // PCIe x4 接口
    output logic                         pcie4_tx_p,
    output logic                         pcie4_tx_n,
    input  logic                         pcie4_rx_p,
    input  logic                         pcie4_rx_n,
    
    // ============================================================================
    // USB 接口 (USB 3.2)
    // ============================================================================
    
    output logic [5:0]                  usb_dp,
    output logic [5:0]                  usb_dn,
    input  logic [5:0]                  usb_vp,
    input  logic [5:0]                  usb_vm,
    output logic                         usb_vbus,
    
    // ============================================================================
    // Ethernet 接口 (10G + 1G)
    // ============================================================================
    
    // 10G Ethernet
    output logic [63:0]                eth10g_txd,
    output logic                         eth10g_txc,
    input  logic [63:0]                eth10g_rxd,
    input  logic                         eth10g_rxc,
    
    // 1G Ethernet
    output logic [3:0]                  eth1g_txd,
    output logic                         eth1g_txc,
    input  logic [3:0]                  eth1g_rxd,
    input  logic                         eth1g_rxc,
    input  logic                         eth1g_mdio,
    output logic                         eth1g_mdc,
    
    // ============================================================================
    // CAN FD 接口 (8-16 ports)
    // ============================================================================
    
    output logic [15:0]                can_tx,
    input  logic [15:0]                can_rx,
    
    // ============================================================================
    // MIPI CSI-2 接口 (ISP 输入)
    // ============================================================================
    
    output logic [15:0]                mipi_d_p,
    output logic [15:0]                mipi_d_n,
    output logic [15:0]                mipi_c_p,
    output logic [15:0]                mipi_c_n,
    
    // ============================================================================
    // Display 接口 (HDMI 2.0 + DP 1.4)
    // ============================================================================
    
    output logic [3:0]                  hdmi_tx_p,
    output logic [3:0]                  hdmi_tx_n,
    output logic                         hdmi_cec,
    input  logic                         hdmi_hpd,
    
    output logic                         dp_aux_p,
    output logic                         dp_aux_n,
    output logic [3:0]                  dp_main_p,
    output logic [3:0]                  dp_main_n,
    input  logic                         dp_hpd,
    
    // ============================================================================
    // GPIO 接口 (64-128 pins)
    // ============================================================================
    
    inout  wire [127:0]              gpio,
    
    // ============================================================================
    // I2C 接口
    // ============================================================================
    
    output logic                         i2c_scl,
    inout  wire [7:0]                  i2c_sda,
    
    // ============================================================================
    // SPI 接口
    // ============================================================================
    
    output logic                         spi_sclk,
    output logic                         spi_mosi,
    input  logic [7:0]                  spi_miso,
    output logic [7:0]                  spi_cs_n,
    
    // ============================================================================
    // UART 接口
    // ============================================================================
    
    output logic [7:0]                  uart_tx,
    input  logic [7:0]                  uart_rx,
    
    // ============================================================================
    // JTAG 调试接口
    // ============================================================================
    
    input  logic                         jtag_tck,
    input  logic                         jtag_tms,
    input  logic                         jtag_tdi,
    output logic                         jtag_tdo,
    input  logic                         jtag_trst_n
    
);

    // ============================================================================
    // 内部信号声明
    // ============================================================================
    
    // 系统时钟
    logic                         clk_sys;
    logic                         clk_cpu;
    logic                         clk_npu;
    logic                         clk_gpu;
    logic                         clk_ddr;
    
    // 系统复位
    logic                         rst_sys_n;
    logic                         rst_cpu_n;
    logic                         rst_npu_n;
    logic                         rst_gpu_n;
    logic                         rst_ddr_n;
    
    // PLL 时钟
    logic                         pll_lock;
    
    // ============================================================================
    // 时钟复位管理单元实例化
    // ============================================================================
    
    pll_top pll_inst (
        .clk_24mhz    (osc_24mhz),
        .rst_n         (rst_sys_n),
        .pll_lock      (pll_lock)
    );
    
    // PLL 时钟输出
    assign clk_cpu = pll_lock;  // PLL 锁定后使能
    assign clk_npu = pll_lock;
    assign clk_gpu = pll_lock;
    assign clk_ddr = pll_lock;
    
    // 系统复位生成
    assign rst_sys_n = por_n & ext_rst_n;
    assign rst_cpu_n = rst_sys_n;
    assign rst_npu_n = rst_sys_n;
    assign rst_gpu_n = rst_sys_n;
    assign rst_ddr_n = rst_sys_n;

endmodule
