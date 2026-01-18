// Copyright (c) 2026 YaoGuang SoC Project
// All rights reserved

// Module: cpu_cluster_top
// Description: CPU Cluster Top Level Integration
//              8x Cortex-A78AE + 2x Cortex-R52 Lockstep
// Version: 1.0
// Author: Frontend Design Engineer
// Date: 2026-01-19

`timescale 1ns/1ps

module cpu_cluster_top (
    //===========================================
    // Clock and Reset
    //===========================================
    input  wire        clk_a78ae_pclk,          // A78AE Primary Clock
    input  wire        clk_a78ae_sclk,          // A78AE Secondary Clock
    input  wire        clk_r52_pclk,            // R52 Primary Clock
    input  wire        clk_r52_sclk,            // R52 Secondary Clock
    input  wire        clk_debug,               // Debug Clock
    input  wire        rst_n_a78ae_poresetn,    // A78AE POR Reset (active low)
    input  wire        rst_n_a78ae_coresetn,    // A78AE Core Reset (active low)
    input  wire        rst_n_r52_poresetn,      // R52 POR Reset (active low)
    input  wire        rst_n_r52_coresetn,      // R52 Core Reset (active low)
    input  wire        rst_n_debug,             // Debug Reset (active low)

    //===========================================
    // ACE4 Interface - A78AE Cluster to NoC
    //===========================================
    output wire [511:0]  ace_a78ae_awid,        // Write Address ID
    output wire [47:0]   ace_a78ae_awaddr,      // Write Address
    output wire [7:0]    ace_a78ae_awlen,       // Write Burst Length
    output wire [2:0]    ace_a78ae_awsize,      // Write Burst Size
    output wire [1:0]    ace_a78ae_awburst,     // Write Burst Type
    output wire          ace_a78ae_awlock,      // Write Lock
    output wire [3:0]    ace_a78ae_awcache,     // Write Cache
    output wire [2:0]    ace_a78ae_awprot,      // Write Protection
    output wire [3:0]    ace_a78ae_awqos,       // Write QoS
    output wire [5:0]    ace_a78ae_awregion,    // Write Region
    output wire [4:0]    ace_a78ae_awuser,      // Write User
    output wire          ace_a78ae_awvalid,     // Write Address Valid
    input  wire          ace_a78ae_awready,     // Write Address Ready

    output wire [511:0]  ace_a78ae_wdata,       // Write Data
    output wire [63:0]   ace_a78ae_wstrb,       // Write Strobes
    output wire          ace_a78ae_wlast,       // Write Last
    output wire [4:0]    ace_a78ae_wuser,       // Write User
    output wire          ace_a78ae_wvalid,      // Write Data Valid
    input  wire          ace_a78ae_wready,      // Write Data Ready

    input  wire [1:0]    ace_a78ae_bresp,       // Write Response
    input  wire [5:0]    ace_a78ae_bid,         // Write Response ID
    input  wire [4:0]    ace_a78ae_buser,       // Write Response User
    input  wire          ace_a78ae_bvalid,      // Write Response Valid
    output wire          ace_a78ae_bready,      // Write Response Ready

    output wire [511:0]  ace_a78ae_arid,        // Read Address ID
    output wire [47:0]   ace_a78ae_araddr,      // Read Address
    output wire [7:0]    ace_a78ae_arlen,       // Read Burst Length
    output wire [2:0]    ace_a78ae_arsize,      // Read Burst Size
    output wire [1:0]    ace_a78ae_arburst,     // Read Burst Type
    output wire          ace_a78ae_arlock,      // Read Lock
    output wire [3:0]    ace_a78ae_arcache,     // Read Cache
    output wire [2:0]    ace_a78ae_arprot,      // Read Protection
    output wire [3:0]    ace_a78ae_arqos,       // Read QoS
    output wire [5:0]    ace_a78ae_arregion,    // Read Region
    output wire [4:0]    ace_a78ae_aruser,      // Read User
    output wire          ace_a78ae_arvalid,     // Read Address Valid
    input  wire          ace_a78ae_arready,     // Read Address Ready

    input  wire [511:0]  ace_a78ae_rdata,       // Read Data
    input  wire [1:0]    ace_a78ae_rresp,       // Read Response
    input  wire [5:0]    ace_a78ae_rid,         // Read ID
    input  wire          ace_a78ae_rlast,       // Read Last
    input  wire [4:0]    ace_a78ae_ruser,       // Read User
    input  wire          ace_a78ae_rvalid,      // Read Valid
    output wire          ace_a78ae_rready,      // Read Ready

    //===========================================
    // ACE4 Snoop Channel - A78AE
    //===========================================
    input  wire [3:0]    ace_a78ae_awsnoop,     // Write Snoop
    input  wire [4:0]    ace_a78ae_awdomain,    // Write Domain
    input  wire          ace_a78ae_awparity,    // Write Parity
    output wire [3:0]    ace_a78ae_acsnoop,     // Snoop Control
    output wire [4:0]    ace_a78ae_acdomain,    // Snoop Domain
    output wire          ace_a78ae_acparity,    // Snoop Parity

    input  wire [1:0]    ace_a78ae_crresp,      // Snoop Response
    input  wire [5:0]    ace_a78ae_crid,        // Snoop Response ID
    input  wire          ace_a78ae_crvalid,     // Snoop Response Valid
    output wire          ace_a78ae_crready,     // Snoop Response Ready

    output wire [511:0]  ace_a78ae_cddata,      // Snoop Data
    output wire [63:0]   ace_a78ae_cdwstrb,     // Snoop Data Strobes
    output wire          ace_a78ae_cdlast,      // Snoop Data Last
    output wire          ace_a78ae_cdvalid,     // Snoop Data Valid
    input  wire          ace_a78ae_cdready,     // Snoop Data Ready

    //===========================================
    // AXI4 Interface - R52 Cluster
    //===========================================
    output wire [3:0]    axi_r52_awid,          // Write Address ID
    output wire [47:0]   axi_r52_awaddr,        // Write Address
    output wire [7:0]    axi_r52_awlen,         // Write Burst Length
    output wire [2:0]    axi_r52_awsize,        // Write Burst Size
    output wire [1:0]    axi_r52_awburst,       // Write Burst Type
    output wire          axi_r52_awlock,        // Write Lock
    output wire [3:0]    axi_r52_awcache,       // Write Cache
    output wire [2:0]    axi_r52_awprot,        // Write Protection
    output wire [3:0]    axi_r52_awqos,         // Write QoS
    output wire          ace_r52_awvalid,       // Write Address Valid
    input  wire          axi_r52_awready,       // Write Address Ready

    output wire [255:0]  axi_r52_wdata,         // Write Data
    output wire [31:0]   axi_r52_wstrb,         // Write Strobes
    output wire          axi_r52_wlast,         // Write Last
    output wire          axi_r52_wvalid,        // Write Data Valid
    input  wire          axi_r52_wready,        // Write Data Ready

    input  wire [1:0]    axi_r52_bresp,         // Write Response
    input  wire [3:0]    axi_r52_bid,           // Write Response ID
    input  wire          axi_r52_bvalid,        // Write Response Valid
    output wire          axi_r52_bready,        // Write Response Ready

    output wire [3:0]    axi_r52_arid,          // Read Address ID
    output wire [47:0]   axi_r52_araddr,        // Read Address
    output wire [7:0]    axi_r52_arlen,         // Read Burst Length
    output wire [2:0]    axi_r52_arsize,        // Read Burst Size
    output wire [1:0]    axi_r52_arburst,       // Read Burst Type
    output wire          axi_r52_arlock,        // Read Lock
    output wire [3:0]    axi_r52_arcache,       // Read Cache
    output wire [2:0]    axi_r52_arprot,        // Read Protection
    output wire [3:0]    axi_r52_arqos,         // Read QoS
    output wire          axi_r52_arvalid,       // Read Address Valid
    input  wire          axi_r52_arready,       // Read Address Ready

    input  wire [255:0]  axi_r52_rdata,         // Read Data
    input  wire [1:0]    axi_r52_rresp,         // Read Response
    input  wire [3:0]    axi_r52_rid,           // Read ID
    input  wire          axi_r52_rlast,         // Read Last
    input  wire          axi_r52_rvalid,        // Read Valid
    output wire          axi_r52_rready,        // Read Ready

    //===========================================
    // Interrupt Interface
    //===========================================
    input  wire [31:0]   irq_a78ae_ext,         // External Interrupts for A78AE
    input  wire [63:0]   irq_r52_ext,           // External Interrupts for R52
    output wire [7:0]    irq_a78ae_to_pic,      // Interrupts to PIC
    output wire [1:0]    irq_r52_to_pic,        // Interrupts to PIC

    //===========================================
    // GIC-600 SPI Interface
    //===========================================
    output wire [31:0]   gic_spi_target,        // SPI Target
    output wire [10:0]   gic_spi_id,            // SPI ID
    output wire          gic_spi_valid,         // SPI Valid
    input  wire          gic_spi_ready,         // SPI Ready

    //===========================================
    // Timer Interface
    //===========================================
    output wire [3:0]    timer_irq_a78ae,       // Timer IRQ to A78AE
    output wire [1:0]    timer_irq_r52,         // Timer IRQ to R52

    //===========================================
    // Debug Interface (CoreSight)
    //===========================================
    output wire [7:0]    dbg_trig_a78ae,        // Debug Trigger from A78AE
    output wire [1:0]    dbg_trig_r52,          // Debug Trigger from R52
    input  wire [7:0]    dbg_trig_in_a78ae,     // Debug Trigger to A78AE
    input  wire [1:0]    dbg_trig_in_r52,       // Debug Trigger to R52

    output wire [79:0]   trace_a78ae,           // Trace Output A78AE
    output wire          trace_a78ae_valid,     // Trace Valid
    output wire [15:0]   trace_r52,             // Trace Output R52
    output wire          trace_r52_valid,       // Trace Valid

    input  wire          dbg_dap_clk,           // DAP Clock
    input  wire          dbg_dap_rst_n,         // DAP Reset
    input  wire [1:0]    dbg_dap_addr,          // DAP Address
    input  wire [31:0]   dbg_dap_wdata,         // DAP Write Data
    input  wire          dbg_dap_write,         // DAP Write Enable
    output wire [31:0]   dbg_dap_rdata,         // DAP Read Data
    output wire          dbg_dap_ack,           // DAP Acknowledge

    //===========================================
    // Power Management Interface
    //===========================================
    input  wire [7:0]    pwr_a78ae_req,         // Power Request A78AE
    output wire [7:0]    pwr_a78ae_ack,         // Power Acknowledge A78AE
    input  wire [1:0]    pwr_r52_req,           // Power Request R52
    output wire [1:0]    pwr_r52_ack,           // Power Acknowledge R52

    output wire [7:0]    pwr_a78ae_status,      // Power Status A78AE
    output wire [1:0]    pwr_r52_status,        // Power Status R52

    //===========================================
    // Error Interface
    //===========================================
    output wire [31:0]   error_a78ae,           // Error Code A78AE
    output wire          error_a78ae_valid,     // Error Valid
    output wire [31:0]   error_r52,             // Error Code R52
    output wire          error_r52_valid,       // Error Valid

    //===========================================
    // Security Interface
    //===========================================
    input  wire [1:0]    sec_req,               // Security Request
    output wire [1:0]    sec_ack,               // Security Acknowledge
    input  wire [127:0]  sec_key,               // Security Key

    //===========================================
    // DFT Interface
    //===========================================
    input  wire          scan_enable,           // Scan Enable
    input  wire          scan_clk,              // Scan Clock
    input  wire          mbist_enable,          // MBIST Enable
    output wire          mbist_done,            // MBIST Done
    output wire [7:0]    mbist_fail,            // MBIST Fail Status
    input  wire          atpg_mode              // ATPG Mode
);

    //===========================================
    // Parameters
    //===========================================
    parameter A78AE_NUM_CORES = 8;
    parameter R52_NUM_CORES   = 2;

    //===========================================
    // Internal Signals
    //===========================================
    wire [A78AE_NUM_CORES*512-1:0] ace_core_awid;
    wire [A78AE_NUM_CORES*48-1:0]  ace_core_awaddr;
    wire [A78AE_NUM_CORES*8-1:0]   ace_core_awlen;
    wire [A78AE_NUM_CORES*2-1:0]   ace_core_awburst;
    wire [A78AE_NUM_CORES-1:0]     ace_core_awlock;
    wire [A78AE_NUM_CORES*4-1:0]   ace_core_awcache;
    wire [A78AE_NUM_CORES*4-1:0]   ace_core_awqos;
    wire [A78AE_NUM_CORES-1:0]     ace_core_awvalid;
    wire [A78AE_NUM_CORES-1:0]     ace_core_awready;

    wire [A78AE_NUM_CORES*512-1:0] ace_core_wdata;
    wire [A78AE_NUM_CORES*64-1:0]  ace_core_wstrb;
    wire [A78AE_NUM_CORES-1:0]     ace_core_wlast;
    wire [A78AE_NUM_CORES-1:0]     ace_core_wvalid;
    wire [A78AE_NUM_CORES-1:0]     ace_core_wready;

    wire [A78AE_NUM_CORES*2-1:0]   ace_core_bresp;
    wire [A78AE_NUM_CORES-1:0]     ace_core_bvalid;
    wire [A78AE_NUM_CORES-1:0]     ace_core_bready;

    wire [A78AE_NUM_CORES*512-1:0] ace_core_arid;
    wire [A78AE_NUM_CORES*48-1:0]  ace_core_araddr;
    wire [A78AE_NUM_CORES*8-1:0]   ace_core_arlen;
    wire [A78AE_NUM_CORES*2-1:0]   ace_core_arburst;
    wire [A78AE_NUM_CORES-1:0]     ace_core_arlock;
    wire [A78AE_NUM_CORES*4-1:0]   ace_core_arcache;
    wire [A78AE_NUM_CORES*4-1:0]   ace_core_arqos;
    wire [A78AE_NUM_CORES-1:0]     ace_core_arvalid;
    wire [A78AE_NUM_CORES-1:0]     ace_core_arready;

    wire [A78AE_NUM_CORES*512-1:0] ace_core_rdata;
    wire [A78AE_NUM_CORES*2-1:0]   ace_core_rresp;
    wire [A78AE_NUM_CORES-1:0]     ace_core_rlast;
    wire [A78AE_NUM_CORES-1:0]     ace_core_rvalid;
    wire [A78AE_NUM_CORES-1:0]     ace_core_rready;

    wire [R52_NUM_CORES*256-1:0]   axi_core_awdata;
    wire [R52_NUM_CORES*32-1:0]    axi_core_awstrb;
    wire [R52_NUM_CORES-1:0]       axi_core_awlast;
    wire [R52_NUM_CORES-1:0]       axi_core_awvalid;
    wire [R52_NUM_CORES-1:0]       axi_core_awready;

    wire [R52_NUM_CORES*2-1:0]     axi_core_bresp;
    wire [R52_NUM_CORES-1:0]       axi_core_bvalid;
    wire [R52_NUM_CORES-1:0]       axi_core_bready;

    wire [R52_NUM_CORES*256-1:0]   axi_core_ardata;
    wire [R52_NUM_CORES*2-1:0]     axi_core_rresp;
    wire [R52_NUM_CORES-1:0]       axi_core_rlast;
    wire [R52_NUM_CORES-1:0]       axi_core_rvalid;
    wire [R52_NUM_CORES-1:0]       axi_core_rready;

    wire [7:0]   irq_a78ae;
    wire [1:0]   irq_r52;
    wire [7:0]   timer_clken_a78ae;
    wire [1:0]   timer_clken_r52;

    wire        lockstep_error;
    wire [31:0] lockstep_error_code;

    //===========================================
    // A78AE Core Cluster
    //===========================================
    cortex_a78ae_core_x8 u_a78ae_cluster (
        .clk_pclk           (clk_a78ae_pclk),
        .clk_sclk           (clk_a78ae_sclk),
        .rst_n_poresetn     (rst_n_a78ae_poresetn),
        .rst_n_coresetn     (rst_n_a78ae_coresetn),
        .scan_enable        (scan_enable),
        .scan_clk           (scan_clk),
        .mbist_enable       (mbist_enable),
        .mbist_done         (),
        .mbist_fail         (),

        .ace_awid           (ace_core_awid),
        .ace_awaddr         (ace_core_awaddr),
        .ace_awlen          (ace_core_awlen),
        .ace_awsize         ({A78AE_NUM_CORES{3'd6}}),
        .ace_awburst        (ace_core_awburst),
        .ace_awlock         (ace_core_awlock),
        .ace_awcache        (ace_core_awcache),
        .ace_awqos          (ace_core_awqos),
        .ace_awvalid        (ace_core_awvalid),
        .ace_awready        (ace_core_awready),

        .ace_wdata          (ace_core_wdata),
        .ace_wstrb          (ace_core_wstrb),
        .ace_wlast          (ace_core_wlast),
        .ace_wvalid         (ace_core_wvalid),
        .ace_wready         (ace_core_wready),

        .ace_bresp          (ace_core_bresp),
        .ace_bvalid         (ace_core_bvalid),
        .ace_bready         (ace_core_bready),

        .ace_arid           (ace_core_arid),
        .ace_araddr         (ace_core_araddr),
        .ace_arlen          (ace_core_arlen),
        .ace_arsize         ({A78AE_NUM_CORES{3'd6}}),
        .ace_arburst        (ace_core_arburst),
        .ace_arlock         (ace_core_arlock),
        .ace_arcache        (ace_core_arcache),
        .ace_arqos          (ace_core_arqos),
        .ace_arvalid        (ace_core_arvalid),
        .ace_arready        (ace_core_arready),

        .ace_rdata          (ace_core_rdata),
        .ace_rresp          (ace_core_rresp),
        .ace_rlast          (ace_core_rlast),
        .ace_rvalid         (ace_core_rvalid),
        .ace_rready         (ace_core_rready),

        .irq_ext            (irq_a78ae_ext),
        .irq_out            (irq_a78ae),
        .timer_clken        (timer_clken_a78ae),

        .dbg_trig_in        (dbg_trig_in_a78ae),
        .dbg_trig_out       (dbg_trig_a78ae),
        .trace_out          (trace_a78ae),
        .trace_valid        (trace_a78ae_valid),

        .pwr_req            (pwr_a78ae_req),
        .pwr_ack            (pwr_a78ae_ack),
        .pwr_status         (pwr_a78ae_status),

        .error_out          (error_a78ae),
        .error_valid        (error_a78ae_valid),

        .sec_req            ({2{sec_req[0]}}),
        .sec_ack            (),
        .sec_key            (sec_key)
    );

    //===========================================
    // ACE Interconnect to NoC
    //===========================================
    ace_interconnect_8to1 u_ace_interconnect (
        .clk                (clk_a78ae_pclk),
        .rst_n              (rst_n_a78ae_poresetn),

        .core_awid          (ace_core_awid),
        .core_awaddr        (ace_core_awaddr),
        .core_awlen         (ace_core_awlen),
        .core_awburst       (ace_core_awburst),
        .core_awlock        (ace_core_awlock),
        .core_awcache       (ace_core_awcache),
        .core_awqos         (ace_core_awqos),
        .core_awvalid       (ace_core_awvalid),
        .core_awready       (ace_core_awready),

        .core_wdata         (ace_core_wdata),
        .core_wstrb         (ace_core_wstrb),
        .core_wlast         (ace_core_wlast),
        .core_wvalid        (ace_core_wvalid),
        .core_wready        (ace_core_wready),

        .core_bresp         (ace_core_bresp),
        .core_bvalid        (ace_core_bvalid),
        .core_bready        (ace_core_bready),

        .core_arid          (ace_core_arid),
        .core_araddr        (ace_core_araddr),
        .core_arlen         (ace_core_arlen),
        .core_arburst       (ace_core_arburst),
        .core_arlock        (ace_core_arlock),
        .core_arcache       (ace_core_arcache),
        .core_arqos         (ace_core_arqos),
        .core_arvalid       (ace_core_arvalid),
        .core_arready       (ace_core_arready),

        .core_rdata         (ace_core_rdata),
        .core_rresp         (ace_core_rresp),
        .core_rlast         (ace_core_rlast),
        .core_rvalid        (ace_core_rvalid),
        .core_rready        (ace_core_rready),

        .noc_awid           (ace_a78ae_awid),
        .noc_awaddr         (ace_a78ae_awaddr),
        .noc_awlen          (ace_a78ae_awlen),
        .noc_awsize         (ace_a78ae_awsize),
        .noc_awburst        (ace_a78ae_awburst),
        .noc_awlock         (ace_a78ae_awlock),
        .noc_awcache        (ace_a78ae_awcache),
        .noc_awprot         (ace_a78ae_awprot),
        .noc_awqos          (ace_a78ae_awqos),
        .noc_awregion       (ace_a78ae_awregion),
        .noc_awuser         (ace_a78ae_awuser),
        .noc_awvalid        (ace_a78ae_awvalid),
        .noc_awready        (ace_a78ae_awready),

        .noc_wdata          (ace_a78ae_wdata),
        .noc_wstrb          (ace_a78ae_wstrb),
        .noc_wlast          (ace_a78ae_wlast),
        .noc_wuser          (ace_a78ae_wuser),
        .noc_wvalid         (ace_a78ae_wvalid),
        .noc_wready         (ace_a78ae_wready),

        .noc_bresp          (ace_a78ae_bresp),
        .noc_bid            (ace_a78ae_bid),
        .noc_buser          (ace_a78ae_buser),
        .noc_bvalid         (ace_a78ae_bvalid),
        .noc_bready         (ace_a78ae_bready),

        .noc_arid           (ace_a78ae_arid),
        .noc_araddr         (ace_a78ae_araddr),
        .noc_arlen          (ace_a78ae_arlen),
        .noc_arsize         (ace_a78ae_arsize),
        .noc_arburst        (ace_a78ae_arburst),
        .noc_arlock         (ace_a78ae_arlock),
        .noc_arcache        (ace_a78ae_arcache),
        .noc_arprot         (ace_a78ae_arprot),
        .noc_arqos          (ace_a78ae_arqos),
        .noc_arregion       (ace_a78ae_arregion),
        .noc_aruser         (ace_a78ae_aruser),
        .noc_arvalid        (ace_a78ae_arvalid),
        .noc_arready        (ace_a78ae_arready),

        .noc_rdata          (ace_a78ae_rdata),
        .noc_rresp          (ace_a78ae_rresp),
        .noc_rid            (ace_a78ae_rid),
        .noc_rlast          (ace_a78ae_rlast),
        .noc_ruser          (ace_a78ae_ruser),
        .noc_rvalid         (ace_a78ae_rvalid),
        .noc_rready         (ace_a78ae_rready),

        .noc_awsnoop        (ace_a78ae_awsnoop),
        .noc_awdomain       (ace_a78ae_awdomain),
        .noc_awparity       (ace_a78ae_awparity),
        .noc_acsnoop        (ace_a78ae_acsnoop),
        .noc_acdomain       (ace_a78ae_acdomain),
        .noc_acparity       (ace_a78ae_acparity),

        .noc_crresp         (ace_a78ae_crresp),
        .noc_crid           (ace_a78ae_crid),
        .noc_crvalid        (ace_a78ae_crvalid),
        .noc_crready        (ace_a78ae_crready),

        .noc_cddata         (ace_a78ae_cddata),
        .noc_cdwstrb        (ace_a78ae_cdwstrb),
        .noc_cdlast         (ace_a78ae_cdlast),
        .noc_cdvalid        (ace_a78ae_cdvalid),
        .noc_cdready        (ace_a78ae_cdready)
    );

    //===========================================
    // R52 Lockstep Cluster
    //===========================================
    cortex_r52_lockstep u_r52_cluster (
        .clk_pclk           (clk_r52_pclk),
        .clk_sclk           (clk_r52_sclk),
        .rst_n_poresetn     (rst_n_r52_poresetn),
        .rst_n_coresetn     (rst_n_r52_coresetn),
        .scan_enable        (scan_enable),
        .scan_clk           (scan_clk),
        .mbist_enable       (mbist_enable),
        .mbist_done         (),
        .mbist_fail         (),

        .axi_awid           (axi_core_awid),
        .axi_awaddr         (axi_core_awaddr),
        .axi_awlen          (axi_core_awlen),
        .axi_awsize         ({R52_NUM_CORES{3'd5}}),
        .axi_awburst        (axi_core_awburst),
        .axi_awlock         (axi_core_awlock),
        .axi_awcache        (axi_core_awcache),
        .axi_awprot         ({R52_NUM_CORES{3'd0}}),
        .axi_awqos          (axi_core_awqos),
        .axi_awvalid        (axi_core_awvalid),
        .axi_awready        (axi_core_awready),

        .axi_wdata          (axi_core_awdata),
        .axi_wstrb          (axi_core_awstrb),
        .axi_wlast          (axi_core_awlast),
        .axi_wvalid         (axi_core_awvalid),
        .axi_wready         (axi_core_awready),

        .axi_bresp          (axi_core_bresp),
        .axi_bvalid         (axi_core_bvalid),
        .axi_bready         (axi_core_bready),

        .axi_arid           (axi_core_arid),
        .axi_araddr         (axi_core_araddr),
        .axi_arlen          (axi_core_arlen),
        .axi_arsize         ({R52_NUM_CORES{3'd5}}),
        .axi_arburst        (axi_core_arburst),
        .axi_arlock         (axi_core_arlock),
        .axi_arcache        (axi_core_arcache),
        .axi_arprot         ({R52_NUM_CORES{3'd0}}),
        .axi_arqos          (axi_core_arqos),
        .axi_arvalid        (axi_core_arvalid),
        .axi_arready        (axi_core_arready),

        .axi_rdata          (axi_core_ardata),
        .axi_rresp          (axi_core_rresp),
        .axi_rlast          (axi_core_rlast),
        .axi_rvalid         (axi_core_rvalid),
        .axi_rready         (axi_core_rready),

        .irq_ext            (irq_r52_ext),
        .irq_out            (irq_r52),
        .timer_clken        (timer_clken_r52),

        .dbg_trig_in        (dbg_trig_in_r52),
        .dbg_trig_out       (dbg_trig_r52),
        .trace_out          (trace_r52),
        .trace_valid        (trace_r52_valid),

        .pwr_req            (pwr_r52_req),
        .pwr_ack            (pwr_r52_ack),
        .pwr_status         (pwr_r52_status),

        .lockstep_error     (lockstep_error),
        .lockstep_error_code(lockstep_error_code),

        .error_out          (error_r52),
        .error_valid        (error_r52_valid),

        .sec_req            ({2{sec_req[1]}}),
        .sec_ack            (),
        .sec_key            (sec_key)
    );

    //===========================================
    // AXI Interconnect to NoC (R52)
    //===========================================
    axi_interconnect_2to1 u_r52_interconnect (
        .clk                (clk_r52_pclk),
        .rst_n              (rst_n_r52_poresetn),

        .s_awid             (axi_core_awid),
        .s_awaddr           (axi_core_awaddr),
        .s_awlen            (axi_core_awlen),
        .s_awsize           ({R52_NUM_CORES{3'd5}}),
        .s_awburst          (axi_core_awburst),
        .s_awlock           (axi_core_awlock),
        .s_awcache          (axi_core_awcache),
        .s_awprot           ({R52_NUM_CORES{3'd0}}),
        .s_awqos            (axi_core_awqos),
        .s_awvalid          (axi_core_awvalid),
        .s_awready          (axi_core_awready),

        .s_wdata            (axi_core_awdata),
        .s_wstrb            (axi_core_awstrb),
        .s_wlast            (axi_core_awlast),
        .s_wvalid           (axi_core_awvalid),
        .s_wready           (axi_core_awready),

        .s_bresp            (axi_core_bresp),
        .s_bvalid           (axi_core_bvalid),
        .s_bready           (axi_core_bready),

        .s_arid             (axi_core_arid),
        .s_araddr           (axi_core_araddr),
        .s_arlen            (axi_core_arlen),
        .s_arsize           ({R52_NUM_CORES{3'd5}}),
        .s_arburst          (axi_core_arburst),
        .s_arlock           (axi_core_arlock),
        .s_arcache          (axi_core_arcache),
        .s_arprot           ({R52_NUM_CORES{3'd0}}),
        .s_arqos            (axi_core_arqos),
        .s_arvalid          (axi_core_arvalid),
        .s_arready          (axi_core_arready),

        .s_rdata            (axi_core_ardata),
        .s_rresp            (axi_core_rresp),
        .s_rlast            (axi_core_rlast),
        .s_rvalid           (axi_core_rvalid),
        .s_rready           (axi_core_rready),

        .m_awid             (axi_r52_awid),
        .m_awaddr           (axi_r52_awaddr),
        .m_awlen            (axi_r52_awlen),
        .m_awsize           (axi_r52_awsize),
        .m_awburst          (axi_r52_awburst),
        .m_awlock           (axi_r52_awlock),
        .m_awcache          (axi_r52_awcache),
        .m_awprot           (axi_r52_awprot),
        .m_awqos            (axi_r52_awqos),
        .m_awvalid          (axi_r52_awvalid),
        .m_awready          (axi_r52_awready),

        .m_wdata            (axi_r52_wdata),
        .m_wstrb            (axi_r52_wstrb),
        .m_wlast            (axi_r52_wlast),
        .m_wvalid           (axi_r52_wvalid),
        .m_wready           (axi_r52_wready),

        .m_bresp            (axi_r52_bresp),
        .m_bid              (axi_r52_bid),
        .m_bvalid           (axi_r52_bvalid),
        .m_bready           (axi_r52_bready),

        .m_arid             (axi_r52_arid),
        .m_araddr           (axi_r52_araddr),
        .m_arlen            (axi_r52_arlen),
        .m_arsize           (axi_r52_arsize),
        .m_arburst          (axi_r52_arburst),
        .m_arlock           (axi_r52_arlock),
        .m_arcache          (axi_r52_arcache),
        .m_arprot           (axi_r52_arprot),
        .m_arqos            (axi_r52_arqos),
        .m_arvalid          (axi_r52_arvalid),
        .m_arready          (axi_r52_arready),

        .m_rdata            (axi_r52_rdata),
        .m_rresp            (axi_r52_rresp),
        .m_rid              (axi_r52_rid),
        .m_rlast            (axi_r52_rlast),
        .m_rvalid           (axi_r52_rvalid),
        .m_rready           (axi_r52_rready)
    );

    //===========================================
    // GIC-600 Interrupt Controller
    //===========================================
    gic600_controller u_gic (
        .clk                (clk_a78ae_pclk),
        .rst_n              (rst_n_a78ae_poresetn),

        .irq_a78ae_in       (irq_a78ae_ext),
        .irq_r52_in         (irq_r52_ext),
        .irq_a78ae_out      (irq_a78ae),
        .irq_r52_out        (irq_r52),

        .timer_irq_a78ae    (timer_irq_a78ae),
        .timer_irq_r52      (timer_irq_r52),

        .spi_target         (gic_spi_target),
        .spi_id             (gic_spi_id),
        .spi_valid          (gic_spi_valid),
        .spi_ready          (gic_spi_ready),

        .error_out          (),
        .error_valid        ()
    );

    //===========================================
    // Snoop Control Unit
    //===========================================
    snoop_control_unit u_scu (
        .clk                (clk_a78ae_pclk),
        .rst_n              (rst_n_a78ae_poresetn),

        .ace_acsnoop        (ace_a78ae_acsnoop),
        .ace_acdomain       (ace_a78ae_acdomain),
        .ace_acparity       (ace_a78ae_acparity),

        .ace_crresp         (ace_a78ae_crresp),
        .ace_crid           (ace_a78ae_crid),
        .ace_crvalid        (ace_a78ae_crvalid),
        .ace_crready        (ace_a78ae_crready),

        .ace_cddata         (ace_a78ae_cddata),
        .ace_cdwstrb        (ace_a78ae_cdwstrb),
        .ace_cdlast         (ace_a78ae_cdlast),
        .ace_cdvalid        (ace_a78ae_cdvalid),
        .ace_cdready        (ace_a78ae_cdready),

        .core_snoop_req     (),
        .core_snoop_grant   (1'b1),
        .snoop_filter_hit   (),
        .dvm_tlb_invalidate ()
    );

    //===========================================
    // Timer Configuration
    //===========================================
    assign timer_clken_a78ae = 8'hFF;
    assign timer_clken_r52   = 2'h3;

    //===========================================
    // Timer Interrupts to Cores
    //===========================================
    assign timer_irq_a78ae[3:0] = {4{1'b0}};
    assign timer_irq_r52[1:0]   = {2{1'b0}};

    //===========================================
    // Debug Connect
    //===========================================
    assign dbg_dap_rdata = 32'h0;
    assign dbg_dap_ack   = 1'b0;

endmodule
