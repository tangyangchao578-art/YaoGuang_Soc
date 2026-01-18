// ============================================================================
// Module: soc_top
// Description: YaoGuang SoC 顶层模块
// Author: YaoGuang RTL Team
// Version: V1.0
// Date: 2026-01-18
// ============================================================================

`timescale 1ns / 1ps

module soc_top (
    // ============================================================================
    // 外部时钟复位接口
    // ============================================================================
    
    input  logic                         osc_24mhz,        // 24 MHz 主晶振
    input  logic                         osc_32k,          // 32.768 kHz RTC 晶振
    input  logic                         por_n,            // 上电复位 (低有效)
    input  logic                         ext_rst_n,        // 外部复位 (低有效)
    
    // ============================================================================
    // DDR 接口 (LPDDR5 x32)
    // ============================================================================
    
    output logic [15:0]                  ddr_dq_p,         // DDR DQ 正相位
    output logic [15:0]                  ddr_dq_n,         // DDR DQ 负相位
    output logic [1:0]                   ddr_dqs_p,        // DDR DQS 正相位
    output logic [1:0]                   ddr_dqs_n,        // DDR DQS 负相位
    output logic [1:0]                   ddr_dm,           // DDR 数据掩码
    output logic [1:0]                   ddr_dmi,          // DDR DMI
    
    output logic                         ddr_ca,           // DDR CA
    output logic                         ddr_ra,           // DDR RA
    output logic                         ddr_we_n,         // DDR WE#
    output logic [16:0]                  ddr_cs_n,         // DDR CS#
    output logic [1:0]                   ddr_cke,          // DDR CKE
    output logic                         ddr_odt,          // DDR ODT
    
    output logic [7:0]                   ddr_bg,           // DDR Bank Group
    output logic [1:0]                   ddr_ba,           // DDR Bank Address
    output logic [2:0]                   ddr_act_n,        // DDR ACT#
    output logic [15:0]                  ddr_a,            // DDR Address
    
    input  logic                         ddr_phy_clk_p,    // DDR PHY 时钟
    input  logic                         ddr_phy_clk_n,
    input  logic                         ddr_phy_rst_n,
    
    // ============================================================================
    // PCIe 接口 (PCIe Gen4 x8 + x4)
    // ============================================================================
    
    // PCIe x8
    output logic [7:0]                   pcie8_tx_p,
    output logic [7:0]                   pcie8_tx_n,
    input  logic [7:0]                   pcie8_rx_p,
    input  logic [7:0]                   pcie8_rx_n,
    input  logic                         pcie8_refclk_p,
    input  logic                         pcie8_refclk_n,
    input  logic                         pcie8_perst_n,
    output logic                         pcie8_wake_n,
    
    // PCIe x4
    output logic [3:0]                   pcie4_tx_p,
    output logic [3:0]                   pcie4_tx_n,
    input  logic [3:0]                   pcie4_rx_p,
    input  logic [3:0]                   pcie4_rx_n,
    
    // ============================================================================
    // USB 接口 (USB 3.2)
    // ============================================================================
    
    output logic [5:0]                   usb_dp,
    output logic [5:0]                   usb_dn,
    input  logic [5:0]                   usb_vp,
    input  logic [5:0]                   usb_vm,
    output logic [5:0]                  usb_vbus,
    
    // ============================================================================
    // Ethernet 接口 (10G + 1G)
    // ============================================================================
    
    // 10G Ethernet
    output logic [63:0]                  eth10g_txd,
    output logic [7:0]                   eth10g_txc,
    input  logic [63:0]                  eth10g_rxd,
    input  logic [7:0]                   eth10g_rxc,
    
    // 1G Ethernet
    output logic [3:0]                   eth1g_txd,
    output logic                         eth1g_txen,
    input  logic [3:0]                   eth1g_rxd,
    input  logic                         eth1g_rxer,
    output logic                         eth1g_mdio,
    output logic                         eth1g_mdc,
    input  logic                         eth1g_int_n,
    
    // ============================================================================
    // CAN FD 接口 (x8)
    // ============================================================================
    
    output logic [7:0]                   can_tx,
    input  logic [7:0]                   can_rx,
    
    // ============================================================================
    // MIPI CSI-2 接口 (ISP 输入)
    // ============================================================================
    
    output logic [15:0]                  mipi_d_p,
    output logic [15:0]                  mipi_d_n,
    output logic [3:0]                   mipi_c_p,
    output logic [3:0]                   mipi_c_n,
    
    // ============================================================================
    // Display 接口 (HDMI 2.0 + DP 1.4)
    // ============================================================================
    
    // HDMI 2.0
    output logic [3:0]                   hdmi_tx_p,
    output logic [3:0]                   hdmi_tx_n,
    output logic                         hdmi_cec,
    input  logic                         hdmi_hpd,
    
    // DisplayPort 1.4
    output logic                         dp_aux_p,
    output logic                         dp_aux_n,
    output logic [3:0]                   dp_main_p,
    output logic [3:0]                   dp_main_n,
    input  logic                         dp_hpd,
    
    // ============================================================================
    // GPIO 接口 (128-bit)
    // ============================================================================
    
    inout  wire [127:0]                  gpio,
    
    // ============================================================================
    // I2C 接口 (x8)
    // ============================================================================
    
    inout  wire [7:0]                    i2c_scl,
    inout  wire [7:0]                    i2c_sda,
    
    // ============================================================================
    // SPI 接口 (x8)
    // ============================================================================
    
    output logic [7:0]                   spi_sclk,
    output logic [7:0]                   spi_mosi,
    input  logic [7:0]                   spi_miso,
    output logic [7:0]                   spi_cs_n,
    
    // ============================================================================
    // UART 接口 (x8)
    // ============================================================================
    
    output logic [7:0]                   uart_tx,
    input  logic [7:0]                   uart_rx,
    
    // ============================================================================
    // Audio 接口
    // ============================================================================
    
    output logic [3:0]                   audio_mclk,
    output logic [3:0]                   audio_bclk,
    output logic [3:0]                   audio_lrclk,
    input  logic [3:0]                   audio_din,
    output logic [3:0]                   audio_dout,
    
    // ============================================================================
    // JTAG 调试接口
    // ============================================================================
    
    input  logic                         jtag_tck,
    input  logic                         jtag_tms,
    input  logic                         jtag_tdi,
    output logic                         jtag_tdo,
    input  logic                         jtag_trst_n,
    
    // ============================================================================
    // 启动模式选择
    // ============================================================================
    
    input  logic [2:0]                   boot_mode,
    
    // ============================================================================
    // 状态指示
    // ============================================================================
    
    output logic                         led_status,
    output logic                         led_error
);
    
    // ============================================================================
    // 包含公共包
    // ============================================================================
    
    `include "soc_package.sv"
    
    // ============================================================================
    // 时钟与复位
    // ============================================================================
    
    logic                                clk_core;
    logic                                clk_safety;
    logic                                clk_npu;
    logic                                clk_gpu;
    logic                                clk_isp;
    logic                                clk_noc;
    logic                                clk_mem;
    logic                                clk_sys;
    logic                                clk_usb;
    logic                                clk_pcie;
    logic                                clk_eth;
    logic                                clk_rtc;
    
    logic                                rst_core_n;
    logic                                rst_safety_n;
    logic                                rst_npu_n;
    logic                                rst_gpu_n;
    logic                                rst_isp_n;
    logic                                rst_noc_n;
    logic                                rst_mem_n;
    logic                                rst_sys_n;
    logic                                rst_pcie_n;
    logic                                rst_usb_n;
    logic                                rst_eth_n;
    logic                                rst_rtc_n;
    
    logic                                pll_main_lock;
    logic                                pll_ddr_lock;
    logic                                pll_peri_lock;
    logic                                pll_usb_lock;
    logic                                pll_pcie_lock;
    logic                                pll_eth_lock;
    
    logic                                init_done;
    
    // ============================================================================
    // 时钟复位管理实例化
    // ============================================================================
    
    soc_clock_reset u_clock_reset (
        .osc_24mhz            (osc_24mhz),
        .osc_32k              (osc_32k),
        .por_n                (por_n),
        .ext_rst_n            (ext_rst_n),
        
        .clk_core             (clk_core),
        .clk_safety           (clk_safety),
        .clk_npu              (clk_npu),
        .clk_gpu              (clk_gpu),
        .clk_isp              (clk_isp),
        .clk_noc              (clk_noc),
        .clk_mem              (clk_mem),
        .clk_sys              (clk_sys),
        .clk_usb              (clk_usb),
        .clk_pcie             (clk_pcie),
        .clk_eth              (clk_eth),
        .clk_rtc              (clk_rtc),
        
        .rst_core_n           (rst_core_n),
        .rst_safety_n         (rst_safety_n),
        .rst_npu_n            (rst_npu_n),
        .rst_gpu_n            (rst_gpu_n),
        .rst_isp_n            (rst_isp_n),
        .rst_noc_n            (rst_noc_n),
        .rst_mem_n            (rst_mem_n),
        .rst_sys_n            (rst_sys_n),
        .rst_pcie_n           (rst_pcie_n),
        .rst_usb_n            (rst_usb_n),
        .rst_eth_n            (rst_eth_n),
        .rst_rtc_n            (rst_rtc_n),
        
        .pll_main_lock        (pll_main_lock),
        .pll_ddr_lock         (pll_ddr_lock),
        .pll_peri_lock        (pll_peri_lock),
        .pll_usb_lock         (pll_usb_lock),
        .pll_pcie_lock        (pll_pcie_lock),
        .pll_eth_lock         (pll_eth_lock),
        
        .cg_cpu_en            (1'b1),
        .cg_npu_en            (1'b1),
        .cg_gpu_en            (1'b1),
        .cg_isp_en            (1'b1),
        .cg_sys_en            (1'b1),
        
        .pwr_domain_on        ({12{1'b1}}),
        .global_reset         (1'b0),
        .reset_status         (),
        .watchdog_timeout     (),
        
        .init_done            (init_done)
    );
    
    // ============================================================================
    // 电源域管理
    // ============================================================================
    
    logic [11:0]                         pwr_on_req;
    logic [11:0]                         pwr_on_ack;
    logic [11:0]                         pwr_state;
    
    soc_power_domain u_power_domain (
        .clk                  (clk_sys),
        .rst_n                (rst_sys_n),
        
        .pwr_on_req           (pwr_on_req),
        .pwr_off_req          ({12{1'b0}}),
        .retention_req        ({12{1'b0}}),
        
        .pwr_on_ack           (pwr_on_ack),
        .pwr_off_ack          (),
        .retention_ack        (),
        .pwr_state            (pwr_state),
        .pwr_good             (),
        .isolation_en         (),
        
        .pwr_gate_en          (),
        .ret_gate_en          (),
        .iso_p_on             (),
        .iso_n_on             (),
        
        .all_domains_on       (),
        .any_domain_off       (),
        .pwr_sequence_err     (),
        .pwr_err_code         ()
    );
    
    // ============================================================================
    // NoC 互联实例化
    // ============================================================================
    
    noc_top u_noc (
        .clk_noc              (clk_noc),
        .rst_noc_n            (rst_noc_n),
        
        // CPU Cluster 接口
        .cpu_ace4_awvalid     (),
        .cpu_ace4_awready     (),
        .cpu_ace4_awaddr      (),
        .cpu_ace4_awlen       (),
        .cpu_ace4_awsize      (),
        .cpu_ace4_awburst     (),
        .cpu_ace4_awqos       (),
        .cpu_ace4_awdomain    (),
        .cpu_ace4_awcache     (),
        
        .cpu_ace4_arvalid     (),
        .cpu_ace4_arready     (),
        .cpu_ace4_araddr      (),
        .cpu_ace4_arlen       (),
        .cpu_ace4_arsize      (),
        .cpu_ace4_arburst     (),
        .cpu_ace4_arqos       (),
        .cpu_ace4_ardomain    (),
        .cpu_ace4_arcache     (),
        
        // NPU Cluster 接口
        .npu_axil_awvalid     (),
        .npu_axil_awready     (),
        .npu_axil_awaddr      (),
        .npu_axil_wvalid      (),
        .npu_axil_wready      (),
        .npu_axil_wdata       (),
        .npu_axil_wstrb       (),
        .npu_axil_bvalid      (),
        .npu_axil_bready      (),
        .npu_axil_bresp       (),
        .npu_axil_arvalid     (),
        .npu_axil_arready     (),
        .npu_axil_araddr      (),
        .npu_axil_rvalid      (),
        .npu_axil_rready      (),
        .npu_axil_rdata       (),
        .npu_axil_rresp       (),
        
        // DDR 控制器接口
        .ddr_axil_awvalid     (),
        .ddr_axil_awready     (),
        .ddr_axil_awaddr      (),
        .ddr_axil_wvalid      (),
        .ddr_axil_wready      (),
        .ddr_axil_wdata       (),
        .ddr_axil_wstrb       (),
        .ddr_axil_bvalid      (),
        .ddr_axil_bready      (),
        .ddr_axil_bresp       (),
        .ddr_axil_arvalid     (),
        .ddr_axil_arready     (),
        .ddr_axil_araddr      (),
        .ddr_axil_rvalid      (),
        .ddr_axil_rready      (),
        .ddr_axil_rdata       (),
        .ddr_axil_rresp       (),
        
        // 外设接口
        .periph_axil_awvalid  (),
        .periph_axil_awready  (),
        .periph_axil_awaddr   (),
        .periph_axil_wvalid   (),
        .periph_axil_wready   (),
        .periph_axil_wdata    (),
        .periph_axil_wstrb    (),
        .periph_axil_bvalid   (),
        .periph_axil_bready   (),
        .periph_axil_bresp    (),
        .periph_axil_arvalid  (),
        .periph_axil_arready  (),
        .periph_axil_araddr   (),
        .periph_axil_rvalid   (),
        .periph_axil_rready   (),
        .periph_axil_rdata    (),
        .periph_axil_rresp    ()
    );
    
    // ============================================================================
    // 引脚复用实例化
    // ============================================================================
    
    soc_pin_mux u_pin_mux (
        .clk                  (clk_sys),
        .rst_n                (rst_sys_n),
        
        .psel                 (1'b0),
        .penable              (1'b0),
        .paddr                (32'h0000_0000),
        .pwrite               (1'b0),
        .pwdata               (32'h0000_0000),
        .prdata               (),
        .pslverr              (),
        .pready               (),
        
        .boot_mode            (boot_mode),
        .func_sel             ({128{4'h0}}),
        
        .gpio_pin             (gpio),
        
        .i2c_scl_pin          (i2c_scl),
        .i2c_sda_pin          (i2c_sda),
        
        .spi_sclk_pin         (spi_sclk),
        .spi_mosi_pin         (spi_mosi),
        .spi_miso_pin         (spi_miso),
        .spi_cs_n_pin         (spi_cs_n),
        
        .uart_tx_pin          (uart_tx),
        .uart_rx_pin          (uart_rx),
        
        .jtag_tck_pin         (jtag_tck),
        .jtag_tms_pin         (jtag_tms),
        .jtag_tdi_pin         (jtag_tdi),
        .jtag_tdo_pin         (jtag_tdo),
        .jtag_trst_n_pin      (jtag_trst_n),
        
        .gpio_o               (),
        .gpio_oe              (),
        .gpio_i               (128'h0),
        
        .i2c_scl_o            (),
        .i2c_scl_oe           (),
        .i2c_scl_i            (8'h0),
        .i2c_sda_o            (),
        .i2c_sda_oe           (),
        .i2c_sda_i            (8'h0),
        
        .spi_sclk_o           (),
        .spi_mosi_o           (),
        .spi_miso_i           (8'h0),
        .spi_cs_n_o           (),
        
        .uart_tx_o            (),
        .uart_rx_i            (8'h0),
        
        .jtag_tck_i           (jtag_tck),
        .jtag_tms_i           (jtag_tms),
        .jtag_tdi_i           (jtag_tdi),
        .jtag_tdo_o           (jtag_tdo),
        .jtag_trst_n_i        (jtag_trst_n),
        
        .dbg_req              (),
        .dbg_ack              (1'b0)
    );
    
    // ============================================================================
    // 胶合逻辑实例化
    // ============================================================================
    
    soc_glue_logic u_glue_logic (
        .clk_sys              (clk_sys),
        .clk_noc              (clk_noc),
        .rst_sys_n            (rst_sys_n),
        .rst_noc_n            (rst_noc_n),
        
        .irq_safety_island    (1'b0),
        .irq_npu              ({4{1'b0}}),
        .irq_gpu              (1'b0),
        .irq_isp              (1'b0),
        .irq_display          (1'b0),
        .irq_pcie             (1'b0),
        .irq_usb              (1'b0),
        .irq_eth              (1'b0),
        .irq_can              ({8{1'b0}}),
        .irq_i2c              ({4{1'b0}}),
        .irq_spi              ({4{1'b0}}),
        .irq_uart             ({8{1'b0}}),
        .irq_gpio             (1'b0),
        .irq_timer            (1'b0),
        .irq_watchdog         (1'b0),
        .irq_rtc              (1'b0),
        .irq_audio            (1'b0),
        .irq_crypto           (1'b0),
        .irq_ddr              (1'b0),
        .irq_error            (1'b0),
        .irq_soft             (1'b0),
        
        .irq_cpu              ({8{1'b0}}),
        .irq_safety_cpu       (),
        
        .m axi_awvalid        (1'b0),
        .m axi_awready        (),
        .m axi_awaddr         (32'h0000_0000),
        .m axi_awlen          (8'h00),
        .m axi_awsize         (3'b000),
        .m axi_awburst        (2'b00),
        
        .m axi_wvalid         (1'b0),
        .m axi_wready         (),
        .m axi_wdata          (32'h0000_0000),
        .m axi_wstrb          (4'h0),
        .m axi_wlast          (1'b0),
        
        .m axi_bvalid         (),
        .m axi_bready         (1'b0),
        .m axi_bresp          (),
        
        .m axi_arvalid        (1'b0),
        .m axi_arready        (),
        .m axi_araddr         (32'h0000_0000),
        .m axi_arlen          (8'h00),
        .m axi_arsize         (3'b000),
        .m axi_arburst        (2'b00),
        
        .m axi_rvalid         (),
        .m axi_rready         (1'b0),
        .m axi_rdata          (),
        .m axi_rresp          (),
        .m axi_rlast          (),
        
        .s apb_paddr          (),
        .s apb_psel           (),
        .s apb_penable        (),
        .s apb_pwrite         (),
        .s apb_pwdata         (),
        .s apb_prdata         (32'h0000_0000),
        .s apb_pslverr        (1'b0),
        .s apb_pready         (1'b1),
        
        .err_addr_decode      (1'b0),
        .err_timeout          (1'b0),
        .err_access           (1'b0),
        .err_security         (1'b0),
        
        .soc_error            (),
        .err_code             (),
        
        .init_done            (init_done),
        .pll_lock             (pll_main_lock),
        .pwr_domain_on        (pwr_on_ack),
        
        .boot_done            (),
        .system_ready         ()
    );
    
    // ============================================================================
    // Boot ROM 实例化
    // ============================================================================
    
    boot_rom_wrapper u_boot_rom (
        .clk                  (clk_sys),
        .rst_n                (rst_sys_n),
        
        .s_awvalid            (1'b0),
        .s_awready            (),
        .s_awaddr             (32'h0000_0000),
        .s_awlen              (8'h00),
        .s_awsize             (3'b000),
        .s_awburst            (2'b00),
        .s_awqos              (4'h0),
        .s_awprot             (4'h0),
        
        .s_wvalid             (1'b0),
        .s_wready             (),
        .s_wdata              (64'h0000_0000_0000_0000),
        .s_wstrb              (8'h00),
        .s_wlast              (1'b0),
        
        .s_bvalid             (),
        .s_bready             (1'b0),
        .s_bresp              (),
        
        .s_arvalid            (1'b0),
        .s_arready            (),
        .s_araddr             (32'h0000_0000),
        .s_arlen              (8'h00),
        .s_arsize             (3'b000),
        .s_arburst            (2'b00),
        .s_arqos              (4'h0),
        .s_arprot             (4'h0),
        
        .s_rvalid             (),
        .s_rready             (1'b0),
        .s_rdata              (),
        .s_rresp              (),
        .s_rlast              (),
        
        .boot_error           (),
        .secure_boot_en       (1'b0),
        .boot_rom_hash        ()
    );
    
    // ============================================================================
    // DDR 物理接口
    // ============================================================================
    
    assign ddr_dq_p      = 16'h0000;
    assign ddr_dq_n      = 16'h0000;
    assign ddr_dqs_p     = 2'b00;
    assign ddr_dqs_n     = 2'b00;
    assign ddr_dm        = 2'b00;
    assign ddr_dmi       = 2'b00;
    assign ddr_ca        = 1'b0;
    assign ddr_ra        = 1'b0;
    assign ddr_we_n      = 1'b1;
    assign ddr_cs_n      = 17'h1FFFF;
    assign ddr_cke       = 2'b00;
    assign ddr_odt       = 1'b0;
    assign ddr_bg        = 8'h00;
    assign ddr_ba        = 2'b00;
    assign ddr_act_n     = 3'b111;
    assign ddr_a         = 16'h0000;
    
    // ============================================================================
    // PCIe 物理接口
    // ============================================================================
    
    assign pcie8_tx_p    = 8'h00;
    assign pcie8_tx_n    = 8'hFF;
    assign pcie8_wake_n  = 1'b1;
    
    assign pcie4_tx_p    = 4'h0;
    assign pcie4_tx_n    = 4'hF;
    
    // ============================================================================
    // USB 物理接口
    // ============================================================================
    
    assign usb_dp        = 6'h00;
    assign usb_dn        = 6'h00;
    assign usb_vbus      = 6'h00;
    
    // ============================================================================
    // Ethernet 物理接口
    // ============================================================================
    
    assign eth10g_txd    = 64'h0000_0000_0000_0000;
    assign eth10g_txc    = 8'h00;
    assign eth1g_txd     = 4'h0;
    assign eth1g_txen    = 1'b0;
    assign eth1g_mdio    = 1'b0;
    assign eth1g_mdc     = 1'b0;
    
    // ============================================================================
    // MIPI 物理接口
    // ============================================================================
    
    assign mipi_d_p      = 16'h0000;
    assign mipi_d_n      = 16'hFFFF;
    assign mipi_c_p      = 4'h0;
    assign mipi_c_n      = 4'hF;
    
    // ============================================================================
    // Display 物理接口
    // ============================================================================
    
    assign hdmi_tx_p     = 4'h0;
    assign hdmi_tx_n     = 4'hF;
    assign hdmi_cec      = 1'b0;
    
    assign dp_aux_p      = 1'b0;
    assign dp_aux_n      = 1'b1;
    assign dp_main_p     = 4'h0;
    assign dp_main_n     = 4'hF;
    
    // ============================================================================
    // Audio 物理接口
    // ============================================================================
    
    assign audio_mclk    = 4'h0;
    assign audio_bclk    = 4'h0;
    assign audio_lrclk   = 4'h0;
    assign audio_dout    = 4'h0;
    
    // ============================================================================
    // CAN 物理接口
    // ============================================================================
    
    assign can_tx        = 8'hFF;
    
    // ============================================================================
    // 状态指示
    // ============================================================================
    
    assign led_status    = init_done;
    assign led_error     = 1'b0;
    
endmodule
