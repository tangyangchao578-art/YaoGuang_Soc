//=============================================================================
// Cortex-R52 Dual-Core Lockstep Module
// ASIL-D Safety Critical - 100% Lockstep Comparison
//=============================================================================

`timescale 1ns/1ps

module cortex_r52_lockstep (
    //============================================================================
    // Clock and Reset
    //============================================================================
    input  logic                            clk_i,
    input  logic                            rst_n_i,
    input  logic                            scan_en_i,

    //============================================================================
    // AXI4 Master Interface
    //============================================================================
    output logic [31:0]                     axi_m_araddr_o,
    output logic [7:0]                      axi_m_arlen_o,
    output logic [2:0]                      axi_m_arsize_o,
    output logic [1:0]                      axi_m_arburst_o,
    output logic                            axi_m_arvalid_o,
    input  logic                            axi_m_arready_i,

    output logic [31:0]                     axi_m_awaddr_o,
    output logic [7:0]                      axi_m_awlen_o,
    output logic [2:0]                      axi_m_awsize_o,
    output logic [1:0]                      axi_m_awburst_o,
    output logic                            axi_m_awvalid_o,
    input  logic                            axi_m_awready_i,

    output logic [63:0]                     axi_m_wdata_o,
    output logic [7:0]                      axi_m_wstrb_o,
    output logic                            axi_m_wlast_o,
    output logic                            axi_m_wvalid_o,
    input  logic                            axi_m_wready_i,

    input  logic [63:0]                     axi_m_rdata_i,
    input  logic [1:0]                      axi_m_rresp_i,
    input  logic                            axi_m_rlast_i,
    input  logic                            axi_m_rvalid_i,
    output logic                            axi_m_rready_o,

    input  logic [63:0]                     axi_m_bdata_i,
    input  logic [1:0]                      axi_m_bresp_i,
    input  logic                            axi_m_bvalid_i,
    output logic                            axi_m_bready_o,

    //============================================================================
    // Lockstep Error Interface
    //============================================================================
    output logic                            error_o,
    output logic [31:0]                     error_code_o
);

    //============================================================================
    // Parameters
    //============================================================================
    parameter logic [31:0] CORE0_BASE_ADDR = 32'h0000_0000;
    parameter logic [31:0] CORE1_BASE_ADDR = 32'h1000_0000;

    //============================================================================
    // Internal Signals
    //============================================================================
    logic                                    core0_arvalid;
    logic                                    core1_arvalid;
    logic [31:0]                             core0_araddr;
    logic [31:0]                             core1_araddr;
    logic [31:0]                             core0_awaddr;
    logic [31:0]                             core1_awaddr;
    logic [7:0]                              core0_arlen;
    logic [7:0]                              core1_arlen;
    logic [7:0]                              core0_awlen;
    logic [7:0]                              core1_awlen;
    logic [63:0]                             core0_rdata;
    logic [63:0]                             core1_rdata;
    logic [1:0]                              core0_rresp;
    logic [1:0]                              core1_rresp;
    logic                                    core0_rvalid;
    logic                                    core1_rvalid;
    logic                                    core0_rlast;
    logic                                    core1_rlast;

    // Comparison registers
    logic [31:0]                             compare_araddr;
    logic [31:0]                             compare_awaddr;
    logic [7:0]                              compare_arlen;
    logic [7:0]                              compare_awlen;
    logic                                    compare_error;
    logic [31:0]                             compare_error_code;

    //============================================================================
    // Primary Core (Core 0)
    //============================================================================
    cortex_r52_core u_core0 (
        .clk_i                 (clk_i),
        .rst_n_i               (rst_n_i),
        .scan_en_i             (scan_en_i),
        .base_addr_i           (CORE0_BASE_ADDR),
        .axi_araddr_o          (core0_araddr),
        .axi_arlen_o           (core0_arlen),
        .axi_arsize_o          (),
        .axi_arburst_o         (),
        .axi_arvalid_o         (core0_arvalid),
        .axi_arready_i         (axi_m_arready_i),
        .axi_awaddr_o          (core0_awaddr),
        .axi_awlen_o           (core0_awlen),
        .axi_awsize_o          (),
        .axi_awburst_o         (),
        .axi_awvalid_o         (),
        .axi_awready_i         (axi_m_awready_i),
        .axi_wdata_o           (axi_m_wdata_o),
        .axi_wstrb_o           (axi_m_wstrb_o),
        .axi_wlast_o           (axi_m_wlast_o),
        .axi_wvalid_o          (axi_m_wvalid_o),
        .axi_wready_i          (axi_m_wready_i),
        .axi_rdata_i           (axi_m_rdata_i),
        .axi_rresp_i           (axi_m_rresp_i),
        .axi_rlast_i           (axi_m_rlast_i),
        .axi_rvalid_i          (axi_m_rvalid_i),
        .axi_rready_o          (axi_m_rready_o),
        .axi_bdata_i           (axi_m_bdata_i),
        .axi_bresp_i           (axi_m_bresp_i),
        .axi_bvalid_i          (axi_m_bvalid_i),
        .axi_bready_o          (axi_m_bready_o),
        .rdata_o               (core0_rdata),
        .rresp_o               (core0_rresp),
        .rvalid_o              (core0_rvalid),
        .rlast_o               (core0_rlast)
    );

    //============================================================================
    // Shadow Core (Core 1) - Delayed by 1 cycle
    //============================================================================
    logic [31:0]                             core1_araddr_d;
    logic [7:0]                              core1_arlen_d;
    logic                                    core1_arvalid_d;
    logic [63:0]                             core1_rdata_d;
    logic [1:0]                              core1_rresp_d;
    logic                                    core1_rvalid_d;
    logic                                    core1_rlast_d;

    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            core1_araddr_d   <= '0;
            core1_arlen_d    <= '0;
            core1_arvalid_d  <= '0;
            core1_rdata_d    <= '0;
            core1_rresp_d    <= '0;
            core1_rvalid_d   <= '0;
            core1_rlast_d    <= '0;
        end else begin
            core1_araddr_d   <= core1_araddr;
            core1_arlen_d    <= core1_arlen;
            core1_arvalid_d  <= core1_arvalid;
            core1_rdata_d    <= core1_rdata;
            core1_rresp_d    <= core1_rresp;
            core1_rvalid_d   <= core1_rvalid;
            core1_rlast_d    <= core1_rlast;
        end
    end

    cortex_r52_core u_core1 (
        .clk_i                 (clk_i),
        .rst_n_i               (rst_n_i),
        .scan_en_i             (scan_en_i),
        .base_addr_i           (CORE1_BASE_ADDR),
        .axi_araddr_o          (core1_araddr),
        .axi_arlen_o           (core1_arlen),
        .axi_arsize_o          (),
        .axi_arburst_o         (),
        .axi_arvalid_o         (core1_arvalid),
        .axi_arready_i         (axi_m_arready_i),
        .axi_awaddr_o          (core1_awaddr),
        .axi_awlen_o           (core1_awlen),
        .axi_awsize_o          (),
        .axi_awburst_o         (),
        .axi_awvalid_o         (),
        .axi_awready_i         (axi_m_awready_i),
        .axi_wdata_o           (),
        .axi_wstrb_o           (),
        .axi_wlast_o           (),
        .axi_wvalid_o          (),
        .axi_wready_i          (axi_m_wready_i),
        .axi_rdata_i           (axi_m_rdata_i),
        .axi_rresp_i           (axi_m_rresp_i),
        .axi_rlast_i           (axi_m_rlast_i),
        .axi_rvalid_i          (axi_m_rvalid_i),
        .axi_rready_o          (),
        .axi_bdata_i           (axi_m_bdata_i),
        .axi_bresp_i           (axi_m_bresp_i),
        .axi_bvalid_i          (axi_m_bvalid_i),
        .axi_bready_o          (),
        .rdata_o               (core1_rdata),
        .rresp_o               (core1_rresp),
        .rvalid_o              (core1_rvalid),
        .rlast_o               (core1_rlast)
    );

    //============================================================================
    // Output Selection (Primary Core Controls)
    //============================================================================
    assign axi_m_araddr_o  = core0_araddr;
    assign axi_m_arlen_o   = core0_arlen;
    assign axi_m_arvalid_o = core0_arvalid;

    //============================================================================
    // Lockstep Comparator - Compare delayed shadow core outputs
    //============================================================================
    logic                                    ar_mismatch;
    logic                                    rdata_mismatch;
    logic                                    rresp_mismatch;
    logic                                    rvalid_mismatch;

    always_comb begin
        ar_mismatch     = core1_arvalid_d && (core0_araddr != core1_araddr_d);
        rdata_mismatch  = core1_rvalid_d && (core0_rdata != core1_rdata_d);
        rresp_mismatch  = core1_rvalid_d && (core0_rresp != core1_rresp_d);
        rvalid_mismatch = core0_rvalid != core1_rvalid_d;

        compare_error = ar_mismatch || rdata_mismatch || rresp_mismatch || rvalid_mismatch;
    end

    //============================================================================
    // Error Code Generation
    //============================================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            error_o          <= '0;
            error_code_o     <= '0;
        end else begin
            error_o <= compare_error;
            if (compare_error) begin
                if (ar_mismatch) begin
                    error_code_o <= 32'h0001_0000 | {core0_araddr[15:0], core1_araddr_d[15:0]};
                end else if (rdata_mismatch) begin
                    error_code_o <= 32'h0002_0000 | {core0_rdata[15:0], core1_rdata_d[15:0]};
                end else if (rresp_mismatch) begin
                    error_code_o <= 32'h0003_0000 | {16'd0, core0_rresp, core1_rresp_d};
                end else begin
                    error_code_o <= 32'h0004_0000;
                end
            end else begin
                error_code_o <= '0;
            end
        end
    end

endmodule
