//=============================================================================
// Safety Island Top Level Module
// ASIL-D Safety Critical Module
//=============================================================================

`timescale 1ns/1ps

module safety_island_top (
    //============================================================================
    // Clock and Reset
    //============================================================================
    input  logic                            clk_main_i,
    input  logic                            clk_safety_i,
    input  logic                            rst_n_main_i,
    input  logic                            rst_n_safety_i,

    //============================================================================
    // AXI4 Master Interface (to NoC)
    //============================================================================
    output logic [31:0]                     m axi_araddr_o,
    output logic [7:0]                      m axi_arlen_o,
    output logic [2:0]                      m axi_arsize_o,
    output logic [1:0]                      m axi_arburst_o,
    output logic                            m axi_arvalid_o,
    input  logic                            m axi_arready_i,

    output logic [31:0]                     m axi_awaddr_o,
    output logic [7:0]                      m axi_awlen_o,
    output logic [2:0]                      m axi_awsize_o,
    output logic [1:0]                      m axi_awburst_o,
    output logic                            m axi_awvalid_o,
    input  logic                            m axi_awready_i,

    output logic [63:0]                     m axi_wdata_o,
    output logic [7:0]                      m axi_wstrb_o,
    output logic                            m axi_wlast_o,
    output logic                            m axi_wvalid_o,
    input  logic                            m axi_wready_i,

    input  logic [63:0]                     m axi_rdata_i,
    input  logic [1:0]                      m axi_rresp_i,
    input  logic                            m axi_rlast_i,
    input  logic                            m axi_rvalid_i,
    output logic                            m axi_rready_o,

    input  logic [63:0]                     m axi_bdata_i,
    input  logic [1:0]                      m axi_bresp_i,
    input  logic                            m axi_bvalid_i,
    output logic                            m axi_bready_o,

    //============================================================================
    // AXI4 Slave Interface (from CPU cluster)
    //============================================================================
    input  logic [31:0]                     s axi_araddr_i,
    input  logic [7:0]                      s axi_arlen_i,
    input  logic [2:0]                      s axi_arsize_i,
    input  logic [1:0]                      s axi_arburst_i,
    input  logic                            s axi_arvalid_i,
    output logic                            s axi_arready_o,

    input  logic [31:0]                     s axi_awaddr_i,
    input  logic [7:0]                      s axi_awlen_i,
    input  logic [2:0]                      s axi_awsize_i,
    input  logic [1:0]                      s axi_awburst_i,
    input  logic                            s axi_awvalid_i,
    output logic                            s axi_awready_o,

    input  logic [63:0]                     s axi_wdata_i,
    input  logic [7:0]                      s axi_wstrb_i,
    input  logic                            s axi_wlast_i,
    input  logic                            s axi_wvalid_i,
    output logic                            s axi_wready_o,

    output logic [63:0]                     s axi_rdata_o,
    output logic [1:0]                      s axi_rresp_o,
    output logic                            s axi_rlast_o,
    output logic                            s axi_rvalid_o,
    input  logic                            s axi_rready_i,

    output logic [63:0]                     s axi_bdata_o,
    output logic [1:0]                      s axi_bresp_o,
    output logic                            s axi_bvalid_o,
    input  logic                            s axi_bready_i,

    //============================================================================
    // Interrupt Interface (to GIC)
    //============================================================================
    output logic [63:0]                     irq_o,
    output logic                            irq_lockstep_o,
    output logic                            irq_ecc_o,
    output logic                            irq_watchdog_o,
    output logic                            irq_fault_o,

    //============================================================================
    // External Watchdog Interface
    //============================================================================
    output logic                            watchdog_pulse_o,
    input  logic                            watchdog_feedback_i,

    //============================================================================
    // Error Reporting
    //============================================================================
    output logic [31:0]                     error_code_o,
    output logic                            error_valid_o,

    //============================================================================
    // Configuration
    //============================================================================
    input  logic [31:0]                     cfg_base_addr_i,
    input  logic                            cfg_enable_i,

    //============================================================================
    // DFT and Safety BIST
    //============================================================================
    input  logic                            scan_en_i,
    input  logic                            mbist_en_i,
    input  logic                            bist_start_i,
    output logic                            bist_done_o,
    output logic [7:0]                      bist_result_o
);

    //============================================================================
    // Internal Signals
    //============================================================================
    logic                                    lockstep_error;
    logic [31:0]                             lockstep_error_code;
    logic                                    ecc_error;
    logic [31:0]                             ecc_error_code;
    logic                                    watchdog_timeout;
    logic                                    watchdog_error;
    logic                                    clk_safety_gated;
    logic                                    rst_n_safety_synced;
    logic [31:0]                             sram_addr;
    logic [63:0]                             sram_wdata;
    logic [63:0]                             sram_rdata;
    logic                                    sram_we;
    logic [7:0]                              sram_wstrb;
    logic                                    sram_init_done;

    //============================================================================
    // Clock and Reset Management
    //============================================================================
    safe_clock_reset u_safe_clk_rst (
        .clk_main_i            (clk_main_i),
        .clk_safety_i          (clk_safety_i),
        .rst_n_main_i          (rst_n_main_i),
        .rst_n_safety_i        (rst_n_safety_i),
        .scan_en_i             (scan_en_i),
        .clk_safety_gated_o    (clk_safety_gated),
        .rst_n_safety_synced_o (rst_n_safety_synced)
    );

    //============================================================================
    // Cortex-R52 Dual-Core Lockstep
    //============================================================================
    cortex_r52_lockstep u_r52_lockstep (
        .clk_i                 (clk_safety_gated),
        .rst_n_i               (rst_n_safety_synced),
        .scan_en_i             (scan_en_i),
        .axi_m_araddr_o        (m axi_araddr_o),
        .axi_m_arlen_o         (m axi_arlen_o),
        .axi_m_arsize_o        (m axi_arsize_o),
        .axi_m_arburst_o       (m axi_arburst_o),
        .axi_m_arvalid_o       (m axi_arvalid_o),
        .axi_m_arready_i       (m axi_arready_i),
        .axi_m_awaddr_o        (m axi_awaddr_o),
        .axi_m_awlen_o         (m axi_awlen_o),
        .axi_m_awsize_o        (m axi_awsize_o),
        .axi_m_awburst_o       (m axi_awburst_o),
        .axi_m_awvalid_o       (m axi_awvalid_o),
        .axi_m_awready_i       (m axi_awready_i),
        .axi_m_wdata_o         (m axi_wdata_o),
        .axi_m_wstrb_o         (m axi_wstrb_o),
        .axi_m_wlast_o         (m axi_wlast_o),
        .axi_m_wvalid_o        (m axi_wvalid_o),
        .axi_m_wready_i        (m axi_wready_i),
        .axi_m_rdata_i         (m axi_rdata_i),
        .axi_m_rresp_i         (m axi_rresp_i),
        .axi_m_rlast_i         (m axi_rlast_i),
        .axi_m_rvalid_i        (m axi_rvalid_i),
        .axi_m_rready_o        (m axi_rready_o),
        .axi_m_bdata_i         (m axi_bdata_i),
        .axi_m_bresp_i         (m axi_bresp_i),
        .axi_m_bvalid_i        (m axi_bvalid_i),
        .axi_m_bready_o        (m axi_bready_o),
        .error_o               (lockstep_error),
        .error_code_o          (lockstep_error_code)
    );

    //============================================================================
    // ECC Memory Controller
    //============================================================================
    ecc_memory_controller u_ecc_ctrl (
        .clk_i                 (clk_safety_gated),
        .rst_n_i               (rst_n_safety_synced),
        .scan_en_i             (scan_en_i),
        .sram_addr_o           (sram_addr),
        .sram_wdata_o          (sram_wdata),
        .sram_rdata_i          (sram_rdata),
        .sram_we_o             (sram_we),
        .sram_wstrb_o          (sram_wstrb),
        .sram_init_done_i      (sram_init_done),
        .axi_s_araddr_i        (s axi_araddr_i),
        .axi_s_arlen_i         (s axi_arlen_i),
        .axi_s_arsize_i        (s axi_arsize_i),
        .axi_s_arburst_i       (s axi_arburst_i),
        .axi_s_arvalid_i       (s axi_arvalid_i),
        .axi_s_arready_o       (s axi_arready_o),
        .axi_s_awaddr_i        (s axi_awaddr_i),
        .axi_s_awlen_i         (s axi_awlen_i),
        .axi_s_awsize_i        (s axi_awsize_i),
        .axi_s_awburst_i       (s axi_awburst_i),
        .axi_s_awvalid_i       (s axi_awvalid_i),
        .axi_s_awready_o       (s axi_awready_o),
        .axi_s_wdata_i         (s axi_wdata_i),
        .axi_s_wstrb_i         (s axi_wstrb_i),
        .axi_s_wlast_i         (s axi_wlast_i),
        .axi_s_wvalid_i        (s axi_wvalid_i),
        .axi_s_wready_o        (s axi_wready_o),
        .axi_s_rdata_o         (s axi_rdata_o),
        .axi_s_rresp_o         (s axi_rresp_o),
        .axi_s_rlast_o         (s axi_rlast_o),
        .axi_s_rvalid_o        (s axi_rvalid_o),
        .axi_s_rready_i        (s axi_rready_i),
        .axi_s_bdata_o         (s axi_bdata_o),
        .axi_s_bresp_o         (s axi_bresp_o),
        .axi_s_bvalid_o        (s axi_bvalid_o),
        .axi_s_bready_i        (s axi_bready_i),
        .error_o               (ecc_error),
        .error_code_o          (ecc_error_code),
        .mbist_en_i            (mbist_en_i),
        .bist_start_i          (bist_start_i),
        .bist_done_o           (bist_done_o),
        .bist_result_o         (bist_result_o)
    );

    //============================================================================
    // Safety Watchdog
    //============================================================================
    safety_watchdog u_watchdog (
        .clk_i                 (clk_safety_i),
        .rst_n_i               (rst_n_safety_i),
        .scan_en_i             (scan_en_i),
        .timeout_o             (watchdog_timeout),
        .error_o               (watchdog_error),
        .pulse_o               (watchdog_pulse_o),
        .feedback_i            (watchdog_feedback_i),
        .cfg_enable_i          (cfg_enable_i),
        .lockstep_error_i      (lockstep_error),
        .ecc_error_i           (ecc_error),
        .kick_i                (1'b1)
    );

    //============================================================================
    // Fault Injection Unit (for BIST)
    //============================================================================
    fault_injection_unit u_fault_inj (
        .clk_i                 (clk_safety_gated),
        .rst_n_i               (rst_n_safety_synced),
        .scan_en_i             (scan_en_i),
        .lockstep_error_i      (lockstep_error),
        .ecc_error_i           (ecc_error),
        .watchdog_error_i      (watchdog_error),
        .sram_addr_o           (sram_addr),
        .sram_wdata_o          (sram_wdata),
        .sram_rdata_i          (sram_rdata),
        .sram_we_o             (sram_we),
        .sram_wstrb_o          (sram_wstrb),
        .enable_i              (mbist_en_i),
        .bist_done_o           (sram_init_done)
    );

    //============================================================================
    // Error Reporting Unit
    //============================================================================
    error_reporting_unit u_err_rpt (
        .clk_i                 (clk_safety_gated),
        .rst_n_i               (rst_n_safety_synced),
        .lockstep_error_i      (lockstep_error),
        .lockstep_error_code_i (lockstep_error_code),
        .ecc_error_i           (ecc_error),
        .ecc_error_code_i      (ecc_error_code),
        .watchdog_error_i      (watchdog_error),
        .watchdog_timeout_i    (watchdog_timeout),
        .error_code_o          (error_code_o),
        .error_valid_o         (error_valid_o),
        .irq_lockstep_o        (irq_lockstep_o),
        .irq_ecc_o             (irq_ecc_o),
        .irq_watchdog_o        (irq_watchdog_o)
    );

    //============================================================================
    // IRQ Aggregation
    //============================================================================
    assign irq_o[0]  = lockstep_error;
    assign irq_o[1]  = ecc_error;
    assign irq_o[2]  = watchdog_timeout | watchdog_error;
    assign irq_o[3]  = 1'b0;
    assign irq_o[63:4] = '0;
    assign irq_fault_o = lockstep_error | ecc_error | watchdog_error;

endmodule
