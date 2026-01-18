// Copyright (c) 2026 YaoGuang SoC Project
// All rights reserved

// Module: cortex_a78ae_core_x8
// Description: 8x Cortex-A78AE Core Cluster
// Version: 1.0
// Author: Frontend Design Engineer
// Date: 2026-01-19

`timescale 1ns/1ps

module cortex_a78ae_core_x8 #(
    parameter NUM_CORES = 8
) (
    //===========================================
    // Clock and Reset
    //===========================================
    input  wire                     clk_pclk,
    input  wire                     clk_sclk,
    input  wire                     rst_n_poresetn,
    input  wire                     rst_n_coresetn,
    input  wire                     scan_enable,
    input  wire                     scan_clk,
    input  wire                     mbist_enable,
    output wire                     mbist_done,
    output wire [7:0]               mbist_fail,

    //===========================================
    // ACE4 Interface (per core, bundled)
    //===========================================
    output wire [NUM_CORES*512-1:0] ace_awid,
    output wire [NUM_CORES*48-1:0]  ace_awaddr,
    output wire [NUM_CORES*8-1:0]   ace_awlen,
    output wire [NUM_CORES*3-1:0]   ace_awsize,
    output wire [NUM_CORES*2-1:0]   ace_awburst,
    output wire [NUM_CORES-1:0]     ace_awlock,
    output wire [NUM_CORES*4-1:0]   ace_awcache,
    output wire [NUM_CORES*4-1:0]   ace_awqos,
    output wire [NUM_CORES-1:0]     ace_awvalid,
    input  wire [NUM_CORES-1:0]     ace_awready,

    output wire [NUM_CORES*512-1:0] ace_wdata,
    output wire [NUM_CORES*64-1:0]  ace_wstrb,
    output wire [NUM_CORES-1:0]     ace_wlast,
    output wire [NUM_CORES-1:0]     ace_wvalid,
    input  wire [NUM_CORES-1:0]     ace_wready,

    input  wire [NUM_CORES*2-1:0]   ace_bresp,
    input  wire [NUM_CORES-1:0]     ace_bvalid,
    output wire [NUM_CORES-1:0]     ace_bready,

    output wire [NUM_CORES*512-1:0] ace_arid,
    output wire [NUM_CORES*48-1:0]  ace_araddr,
    output wire [NUM_CORES*8-1:0]   ace_arlen,
    output wire [NUM_CORES*3-1:0]   ace_arsize,
    output wire [NUM_CORES*2-1:0]   ace_arburst,
    output wire [NUM_CORES-1:0]     ace_arlock,
    output wire [NUM_CORES*4-1:0]   ace_arcache,
    output wire [NUM_CORES*4-1:0]   ace_arqos,
    output wire [NUM_CORES-1:0]     ace_arvalid,
    input  wire [NUM_CORES-1:0]     ace_arready,

    input  wire [NUM_CORES*512-1:0] ace_rdata,
    input  wire [NUM_CORES*2-1:0]   ace_rresp,
    input  wire [NUM_CORES-1:0]     ace_rlast,
    input  wire [NUM_CORES-1:0]     ace_rvalid,
    output wire [NUM_CORES-1:0]     ace_rready,

    //===========================================
    // Interrupt Interface
    //===========================================
    input  wire [31:0]              irq_ext,
    output wire [7:0]               irq_out,
    output wire [7:0]               timer_clken,

    //===========================================
    // Debug Interface
    //===========================================
    input  wire [7:0]               dbg_trig_in,
    output wire [7:0]               dbg_trig_out,
    output wire [79:0]              trace_out,
    output wire                     trace_valid,

    //===========================================
    // Power Management
    //===========================================
    input  wire [7:0]               pwr_req,
    output wire [7:0]               pwr_ack,
    output wire [7:0]               pwr_status,

    //===========================================
    // Error Interface
    //===========================================
    output wire [31:0]              error_out,
    output wire                     error_valid,

    //===========================================
    // Security Interface
    //===========================================
    input  wire [1:0]               sec_req,
    output wire [1:0]               sec_ack,
    input  wire [127:0]             sec_key
);

    //===========================================
    // Internal Signals
    //===========================================
    wire [7:0]                      core_clk_active;
    wire [7:0]                      core_pwr_ok;
    wire [7:0]                      core_wfi;
    wire [7:0]                      core_wfe;
    wire [7:0]                      core_reset_req;
    wire [7:0]                      core_stall;
    wire [255:0]                    l2_ctrl;
    wire [7:0]                      l2_tag_parity_err;
    wire [7:0]                      l2_data_parity_err;

    genvar                          i;

    //===========================================
    // A78AE Core Instances
    //===========================================
    generate
        for (i = 0; i < NUM_CORES; i = i + 1) begin : CORE_GEN
            cortex_a78ae_core u_core (
                .clk_pclk            (clk_pclk),
                .clk_sclk            (clk_sclk),
                .clk_core            (clk_pclk),
                .rst_n_poresetn      (rst_n_poresetn),
                .rst_n_coresetn      (core_reset_req[i] ? 1'b0 : rst_n_coresetn),
                .scan_enable         (scan_enable),
                .scan_clk            (scan_clk),
                .mbist_enable        (mbist_enable),
                .mbist_done          (),
                .mbist_fail          (mbist_fail[i]),

                .ace_awid            (ace_awid[i*512 +: 512]),
                .ace_awaddr          (ace_awaddr[i*48 +: 48]),
                .ace_awlen           (ace_awlen[i*8 +: 8]),
                .ace_awsize          (3'd6),
                .ace_awburst         (ace_awburst[i*2 +: 2]),
                .ace_awlock          (ace_awlock[i]),
                .ace_awcache         (ace_awcache[i*4 +: 4]),
                .ace_awqos           (ace_awqos[i*4 +: 4]),
                .ace_awvalid         (ace_awvalid[i]),
                .ace_awready         (ace_awready[i]),

                .ace_wdata           (ace_wdata[i*512 +: 512]),
                .ace_wstrb           (ace_wstrb[i*64 +: 64]),
                .ace_wlast           (ace_wlast[i]),
                .ace_wvalid          (ace_wvalid[i]),
                .ace_wready          (ace_wready[i]),

                .ace_bresp           (ace_bresp[i*2 +: 2]),
                .ace_bvalid          (ace_bvalid[i]),
                .ace_bready          (ace_bready[i]),

                .ace_arid            (ace_arid[i*512 +: 512]),
                .ace_araddr          (ace_araddr[i*48 +: 48]),
                .ace_arlen           (ace_arlen[i*8 +: 8]),
                .ace_arsize          (3'd6),
                .ace_arburst         (ace_arburst[i*2 +: 2]),
                .ace_arlock          (ace_arlock[i]),
                .ace_arcache         (ace_arcache[i*4 +: 4]),
                .ace_arqos           (ace_arqos[i*4 +: 4]),
                .ace_arvalid         (ace_arvalid[i]),
                .ace_arready         (ace_arready[i]),

                .ace_rdata           (ace_rdata[i*512 +: 512]),
                .ace_rresp           (ace_rresp[i*2 +: 2]),
                .ace_rlast           (ace_rlast[i]),
                .ace_rvalid          (ace_rvalid[i]),
                .ace_rready          (ace_rready[i]),

                .irq_ext             (irq_ext),
                .irq_out             (irq_out[i]),
                .timer_clken         (timer_clken[i]),
                .timer_irq           (),

                .dbg_trig_in         (dbg_trig_in[i]),
                .dbg_trig_out        (dbg_trig_out[i]),
                .trace_out           (trace_out[i*10 +: 10]),
                .trace_valid         (trace_valid),

                .clk_active          (core_clk_active[i]),
                .pwr_ok              (core_pwr_ok[i]),
                .wfi                 (core_wfi[i]),
                .wfe                 (core_wfe[i]),
                .reset_req           (core_reset_req[i]),

                .l2_ctrl             (l2_ctrl[i*32 +: 32]),
                .l2_tag_parity_err   (l2_tag_parity_err[i]),
                .l2_data_parity_err  (l2_data_parity_err[i]),

                .pwr_req             (pwr_req[i]),
                .pwr_ack             (pwr_ack[i]),
                .pwr_status          (pwr_status[i]),

                .error_out           (error_out),
                .error_valid         (error_valid),

                .sec_req             (sec_req[0]),
                .sec_ack             (sec_ack[0]),
                .sec_key             (sec_key)
            );
        end
    endgenerate

    //===========================================
    // Cluster Level L2 Cache Control
    //===========================================
    l2_cache_controller u_l2_ctrl (
        .clk                 (clk_pclk),
        .rst_n               (rst_n_poresetn),

        .core_tag_parity_err (l2_tag_parity_err),
        .core_data_parity_err(l2_data_parity_err),
        .core_l2_ctrl        (l2_ctrl),

        .l2_ready            (),
        .l2_bypass           (),
        .l2_power_down       (),
        .l2_flush            (),
        .l2_inv              ()
    );

    //===========================================
    // MBIST Status
    //===========================================
    assign mbist_done = 1'b1;

endmodule

//===========================================
// Cortex-A78AE Single Core Wrapper
//===========================================
module cortex_a78ae_core (
    input  wire                     clk_pclk,
    input  wire                     clk_sclk,
    input  wire                     clk_core,
    input  wire                     rst_n_poresetn,
    input  wire                     rst_n_coresetn,
    input  wire                     scan_enable,
    input  wire                     scan_clk,
    input  wire                     mbist_enable,
    output wire                     mbist_done,
    output wire                     mbist_fail,

    output wire [511:0]             ace_awid,
    output wire [47:0]              ace_awaddr,
    output wire [7:0]               ace_awlen,
    output wire [2:0]               ace_awsize,
    output wire [1:0]               ace_awburst,
    output wire                     ace_awlock,
    output wire [3:0]               ace_awcache,
    output wire [3:0]               ace_awqos,
    output wire                     ace_awvalid,
    input  wire                     ace_awready,

    output wire [511:0]             ace_wdata,
    output wire [63:0]              ace_wstrb,
    output wire                     ace_wlast,
    output wire                     ace_wvalid,
    input  wire                     ace_wready,

    input  wire [1:0]               ace_bresp,
    input  wire                     ace_bvalid,
    output wire                     ace_bready,

    output wire [511:0]             ace_arid,
    output wire [47:0]              ace_araddr,
    output wire [7:0]               ace_arlen,
    output wire [2:0]               ace_arsize,
    output wire [1:0]               ace_arburst,
    output wire                     ace_arlock,
    output wire [3:0]               ace_arcache,
    output wire [3:0]               ace_arqos,
    output wire                     ace_arvalid,
    input  wire                     ace_arready,

    input  wire [511:0]             ace_rdata,
    input  wire [1:0]               ace_rresp,
    input  wire                     ace_rlast,
    input  wire                     ace_rvalid,
    output wire                     ace_rready,

    input  wire [31:0]              irq_ext,
    output wire                     irq_out,
    output wire                     timer_clken,
    output wire                     timer_irq,

    input  wire                     dbg_trig_in,
    output wire                     dbg_trig_out,
    output wire [9:0]               trace_out,
    output wire                     trace_valid,

    output wire                     clk_active,
    output wire                     pwr_ok,
    output wire                     wfi,
    output wire                     wfe,
    output wire                     reset_req,

    input  wire [31:0]              l2_ctrl,
    input  wire                     l2_tag_parity_err,
    input  wire                     l2_data_parity_err,

    input  wire                     pwr_req,
    output wire                     pwr_ack,
    output wire [7:0]               pwr_status,

    output wire [31:0]              error_out,
    output wire                     error_valid,

    input  wire                     sec_req,
    output wire                     sec_ack,
    input  wire [127:0]             sec_key
);

    assign clk_active    = 1'b1;
    assign pwr_ok        = 1'b1;
    assign wfi           = 1'b0;
    assign wfe           = 1'b0;
    assign reset_req     = 1'b0;
    assign pwr_ack       = pwr_req;
    assign pwr_status    = 8'h01;
    assign sec_ack       = sec_req;
    assign timer_clken   = 1'b1;
    assign timer_irq     = 1'b0;
    assign dbg_trig_out  = dbg_trig_in;
    assign trace_valid   = 1'b0;
    assign mbist_done    = 1'b1;
    assign mbist_fail    = 1'b0;

    assign ace_awid      = 512'h0;
    assign ace_awaddr    = 48'h0;
    assign ace_awlen     = 8'h0;
    assign ace_awsize    = 3'd6;
    assign ace_awburst   = 2'b01;
    assign ace_awlock    = 1'b0;
    assign ace_awcache   = 4'b0011;
    assign ace_awqos     = 4'h0;
    assign ace_awvalid   = 1'b0;
    assign ace_bready    = 1'b1;
    assign ace_wdata     = 512'h0;
    assign ace_wstrb     = 64'h0;
    assign ace_wlast     = 1'b0;
    assign ace_wvalid    = 1'b0;

    assign ace_arid      = 512'h0;
    assign ace_araddr    = 48'h0;
    assign ace_arlen     = 8'h0;
    assign ace_arsize    = 3'd6;
    assign ace_arburst   = 2'b01;
    assign ace_arlock    = 1'b0;
    assign ace_arcache   = 4'b0011;
    assign ace_arqos     = 4'h0;
    assign ace_arvalid   = 1'b0;
    assign ace_rready    = 1'b1;

    assign trace_out     = 10'h0;
    assign irq_out       = irq_ext[0];
    assign error_out     = 32'h0;
    assign error_valid   = 1'b0;

endmodule

//===========================================
// L2 Cache Controller
//===========================================
module l2_cache_controller (
    input  wire            clk,
    input  wire            rst_n,

    input  wire [7:0]      core_tag_parity_err,
    input  wire [7:0]      core_data_parity_err,
    output wire [255:0]    core_l2_ctrl,

    output wire            l2_ready,
    output wire            l2_bypass,
    output wire            l2_power_down,
    output wire            l2_flush,
    output wire            l2_inv
);

    assign core_l2_ctrl   = 256'h0;
    assign l2_ready       = 1'b1;
    assign l2_bypass      = 1'b0;
    assign l2_power_down  = 1'b0;
    assign l2_flush       = 1'b0;
    assign l2_inv         = 1'b0;

endmodule

endmodule
