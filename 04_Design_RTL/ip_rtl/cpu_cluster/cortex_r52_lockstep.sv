// Copyright (c) 2026 YaoGuang SoC Project
// All rights reserved

// Module: cortex_r52_lockstep
// Description: 2x Cortex-R52 Dual-Core Lockstep
// Version: 1.0
// Author: Frontend Design Engineer
// Date: 2026-01-19

`timescale 1ns/1ps

module cortex_r52_lockstep #(
    parameter NUM_CORES = 2
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
    output wire [1:0]               mbist_fail,

    //===========================================
    // AXI4 Interface (per core, bundled)
    //===========================================
    output wire [NUM_CORES*4-1:0]   axi_awid,
    output wire [NUM_CORES*48-1:0]  axi_awaddr,
    output wire [NUM_CORES*8-1:0]   axi_awlen,
    output wire [NUM_CORES*3-1:0]   axi_awsize,
    output wire [NUM_CORES*2-1:0]   axi_awburst,
    output wire [NUM_CORES-1:0]     axi_awlock,
    output wire [NUM_CORES*4-1:0]   axi_awcache,
    output wire [NUM_CORES*3-1:0]   axi_awprot,
    output wire [NUM_CORES*4-1:0]   axi_awqos,
    output wire [NUM_CORES-1:0]     axi_awvalid,
    input  wire [NUM_CORES-1:0]     axi_awready,

    output wire [NUM_CORES*256-1:0] axi_wdata,
    output wire [NUM_CORES*32-1:0]  axi_wstrb,
    output wire [NUM_CORES-1:0]     axi_wlast,
    output wire [NUM_CORES-1:0]     axi_wvalid,
    input  wire [NUM_CORES-1:0]     axi_wready,

    input  wire [NUM_CORES*2-1:0]   axi_bresp,
    input  wire [NUM_CORES-1:0]     axi_bvalid,
    output wire [NUM_CORES-1:0]     axi_bready,

    output wire [NUM_CORES*4-1:0]   axi_arid,
    output wire [NUM_CORES*48-1:0]  axi_araddr,
    output wire [NUM_CORES*8-1:0]   axi_arlen,
    output wire [NUM_CORES*3-1:0]   axi_arsize,
    output wire [NUM_CORES*2-1:0]   axi_arburst,
    output wire [NUM_CORES-1:0]     axi_arlock,
    output wire [NUM_CORES*4-1:0]   axi_arcache,
    output wire [NUM_CORES*3-1:0]   axi_arprot,
    output wire [NUM_CORES*4-1:0]   axi_arqos,
    output wire [NUM_CORES-1:0]     axi_arvalid,
    input  wire [NUM_CORES-1:0]     axi_arready,

    input  wire [NUM_CORES*256-1:0] axi_rdata,
    input  wire [NUM_CORES*2-1:0]   axi_rresp,
    input  wire [NUM_CORES-1:0]     axi_rlast,
    input  wire [NUM_CORES-1:0]     axi_rvalid,
    output wire [NUM_CORES-1:0]     axi_rready,

    //===========================================
    // Interrupt Interface
    //===========================================
    input  wire [63:0]              irq_ext,
    output wire [1:0]               irq_out,
    output wire [1:0]               timer_clken,

    //===========================================
    // Debug Interface
    //===========================================
    input  wire [1:0]               dbg_trig_in,
    output wire [1:0]               dbg_trig_out,
    output wire [15:0]              trace_out,
    output wire                     trace_valid,

    //===========================================
    // Power Management
    //===========================================
    input  wire [1:0]               pwr_req,
    output wire [1:0]               pwr_ack,
    output wire [1:0]               pwr_status,

    //===========================================
    // Lockstep Error Interface
    //===========================================
    output wire                     lockstep_error,
    output wire [31:0]              lockstep_error_code,

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
    // Parameters
    //===========================================
    localparam ID_PRIMARY = 4'h0;
    localparam ID_SHADOW  = 4'h1;

    //===========================================
    // Internal Signals
    //===========================================
    wire [255:0]                    primary_ace_awid;
    wire [47:0]                     primary_ace_awaddr;
    wire [7:0]                      primary_ace_awlen;
    wire [2:0]                      primary_ace_awsize;
    wire [1:0]                      primary_ace_awburst;
    wire                            primary_ace_awlock;
    wire [3:0]                      primary_ace_awcache;
    wire [3:0]                      primary_ace_awqos;
    wire                            primary_ace_awvalid;
    wire                            primary_ace_awready;

    wire [255:0]                    primary_ace_wdata;
    wire [31:0]                     primary_ace_wstrb;
    wire                            primary_ace_wlast;
    wire                            primary_ace_wvalid;
    wire                            primary_ace_wready;

    wire [1:0]                      primary_ace_bresp;
    wire                            primary_ace_bvalid;
    wire                            primary_ace_bready;

    wire [255:0]                    primary_ace_arid;
    wire [47:0]                     primary_ace_araddr;
    wire [7:0]                      primary_ace_arlen;
    wire [2:0]                      primary_ace_arsize;
    wire [1:0]                      primary_ace_arburst;
    wire                            primary_ace_arlock;
    wire [3:0]                      primary_ace_arcache;
    wire [3:0]                      primary_ace_arqos;
    wire                            primary_ace_arvalid;
    wire                            primary_ace_arready;

    wire [255:0]                    primary_ace_rdata;
    wire [1:0]                      primary_ace_rresp;
    wire                            primary_ace_rlast;
    wire                            primary_ace_rvalid;
    wire                            primary_ace_rready;

    wire [255:0]                    shadow_ace_awid;
    wire [47:0]                     shadow_ace_awaddr;
    wire [7:0]                      shadow_ace_awlen;
    wire [2:0]                      shadow_ace_awsize;
    wire [1:0]                      shadow_ace_awburst;
    wire                            shadow_ace_awlock;
    wire [3:0]                      shadow_ace_awcache;
    wire [3:0]                      shadow_ace_awqos;
    wire                            shadow_ace_awvalid;
    wire                            shadow_ace_awready;

    wire [255:0]                    shadow_ace_wdata;
    wire [31:0]                     shadow_ace_wstrb;
    wire                            shadow_ace_wlast;
    wire                            shadow_ace_wvalid;
    wire                            shadow_ace_wready;

    wire [1:0]                      shadow_ace_bresp;
    wire                            shadow_ace_bvalid;
    wire                            shadow_ace_bready;

    wire [255:0]                    shadow_ace_arid;
    wire [47:0]                     shadow_ace_araddr;
    wire [7:0]                      shadow_ace_arlen;
    wire [2:0]                      shadow_ace_arsize;
    wire [1:0]                      shadow_ace_arburst;
    wire                            shadow_ace_arlock;
    wire [3:0]                      shadow_ace_arcache;
    wire [3:0]                      shadow_ace_arqos;
    wire                            shadow_ace_arvalid;
    wire                            shadow_ace_arready;

    wire [255:0]                    shadow_ace_rdata;
    wire [1:0]                      shadow_ace_rresp;
    wire                            shadow_ace_rlast;
    wire                            shadow_ace_rvalid;
    wire                            shadow_ace_rready;

    wire                            primary_clk_active;
    wire                            primary_pwr_ok;
    wire                            primary_wfi;
    wire                            primary_wfe;
    wire                            primary_reset_req;
    wire                            shadow_clk_active;
    wire                            shadow_pwr_ok;
    wire                            shadow_wfi;
    wire                            shadow_wfe;
    wire                            shadow_reset_req;

    wire [31:0]                     primary_result_a;
    wire [31:0]                     primary_result_b;
    wire [31:0]                     shadow_result_a;
    wire [31:0]                     shadow_result_b;
    wire                            primary_store_data_valid;
    wire                            shadow_store_data_valid;
    wire [255:0]                    primary_store_data;
    wire [255:0]                    shadow_store_data;
    wire                            primary_store_addr_valid;
    wire                            shadow_store_addr_valid;
    wire [47:0]                     primary_store_addr;
    wire [47:0]                     shadow_store_addr;

    wire                            compare_error;
    wire [5:0]                      compare_error_type;
    reg                             lockstep_error_reg;
    reg  [31:0]                     lockstep_error_code_reg;

    //===========================================
    // Primary Core Instance
    //===========================================
    cortex_r52_core u_primary (
        .clk_pclk            (clk_pclk),
        .clk_sclk            (clk_sclk),
        .rst_n_poresetn      (rst_n_poresetn),
        .rst_n_coresetn      (primary_reset_req ? 1'b0 : rst_n_coresetn),
        .scan_enable         (scan_enable),
        .scan_clk            (scan_clk),
        .mbist_enable        (mbist_enable),
        .mbist_done          (),
        .mbist_fail          (mbist_fail[0]),

        .axi_awid            (primary_ace_awid[3:0]),
        .axi_awaddr          (primary_ace_awaddr),
        .axi_awlen           (primary_ace_awlen),
        .axi_awsize          (primary_ace_awsize),
        .axi_awburst         (primary_ace_awburst),
        .axi_awlock          (primary_ace_awlock),
        .axi_awcache         (primary_ace_awcache),
        .axi_awprot          (3'd0),
        .axi_awqos           (primary_ace_awqos),
        .axi_awvalid         (primary_ace_awvalid),
        .axi_awready         (primary_ace_awready),

        .axi_wdata           (primary_ace_wdata),
        .axi_wstrb           (primary_ace_wstrb),
        .axi_wlast           (primary_ace_wlast),
        .axi_wvalid          (primary_ace_wvalid),
        .axi_wready          (primary_ace_wready),

        .axi_bresp           (primary_ace_bresp),
        .axi_bvalid          (primary_ace_bvalid),
        .axi_bready          (primary_ace_bready),

        .axi_arid            (primary_ace_arid[3:0]),
        .axi_araddr          (primary_ace_araddr),
        .axi_arlen           (primary_ace_arlen),
        .axi_arsize          (primary_ace_arsize),
        .axi_arburst         (primary_ace_arburst),
        .axi_arlock          (primary_ace_arlock),
        .axi_arcache         (primary_ace_arcache),
        .axi_arprot          (3'd0),
        .axi_arqos           (primary_ace_arqos),
        .axi_arvalid         (primary_ace_arvalid),
        .axi_arready         (primary_ace_arready),

        .axi_rdata           (primary_ace_rdata),
        .axi_rresp           (primary_ace_rresp),
        .axi_rlast           (primary_ace_rlast),
        .axi_rvalid          (primary_ace_rvalid),
        .axi_rready          (primary_ace_rready),

        .irq_ext             (irq_ext[31:0]),
        .irq_out             (irq_out[0]),
        .timer_clken         (timer_clken[0]),

        .dbg_trig_in         (dbg_trig_in[0]),
        .dbg_trig_out        (dbg_trig_out[0]),
        .trace_out           (trace_out[7:0]),
        .trace_valid         (trace_valid),

        .clk_active          (primary_clk_active),
        .pwr_ok              (primary_pwr_ok),
        .wfi                 (primary_wfi),
        .wfe                 (primary_wfe),
        .reset_req           (primary_reset_req),

        .pwr_req             (pwr_req[0]),
        .pwr_ack             (pwr_ack[0]),
        .pwr_status          (pwr_status[0]),

        .error_out           (),
        .error_valid         (),

        .sec_req             (sec_req[0]),
        .sec_ack             (sec_ack[0]),
        .sec_key             (sec_key),

        .core_id             (ID_PRIMARY),

        .result_a            (primary_result_a),
        .result_b            (primary_result_b),
        .store_data_valid    (primary_store_data_valid),
        .store_data          (primary_store_data),
        .store_addr_valid    (primary_store_addr_valid),
        .store_addr          (primary_store_addr)
    );

    //===========================================
    // Shadow Core Instance
    //===========================================
    cortex_r52_core u_shadow (
        .clk_pclk            (clk_pclk),
        .clk_sclk            (clk_sclk),
        .rst_n_poresetn      (rst_n_poresetn),
        .rst_n_coresetn      (shadow_reset_req ? 1'b0 : rst_n_coresetn),
        .scan_enable         (scan_enable),
        .scan_clk            (scan_clk),
        .mbist_enable        (mbist_enable),
        .mbist_done          (),
        .mbist_fail          (mbist_fail[1]),

        .axi_awid            (shadow_ace_awid[3:0]),
        .axi_awaddr          (shadow_ace_awaddr),
        .axi_awlen           (shadow_ace_awlen),
        .axi_awsize          (shadow_ace_awsize),
        .axi_awburst         (shadow_ace_awburst),
        .axi_awlock          (shadow_ace_awlock),
        .axi_awcache         (shadow_ace_awcache),
        .axi_awprot          (3'd0),
        .axi_awqos           (shadow_ace_awqos),
        .axi_awvalid         (shadow_ace_awvalid),
        .axi_awready         (shadow_ace_awready),

        .axi_wdata           (shadow_ace_wdata),
        .axi_wstrb           (shadow_ace_wstrb),
        .axi_wlast           (shadow_ace_wlast),
        .axi_wvalid          (shadow_ace_wvalid),
        .axi_wready          (shadow_ace_wready),

        .axi_bresp           (shadow_ace_bresp),
        .axi_bvalid          (shadow_ace_bvalid),
        .axi_bready          (shadow_ace_bready),

        .axi_arid            (shadow_ace_arid[3:0]),
        .axi_araddr          (shadow_ace_araddr),
        .axi_arlen           (shadow_ace_arlen),
        .axi_arsize          (shadow_ace_arsize),
        .axi_arburst         (shadow_ace_arburst),
        .axi_arlock          (shadow_ace_arlock),
        .axi_arcache         (shadow_ace_arcache),
        .axi_arprot          (3'd0),
        .axi_arqos           (shadow_ace_arqos),
        .axi_arvalid         (shadow_ace_arvalid),
        .axi_arready         (shadow_ace_arready),

        .axi_rdata           (shadow_ace_rdata),
        .axi_rresp           (shadow_ace_rresp),
        .axi_rlast           (shadow_ace_rlast),
        .axi_rvalid          (shadow_ace_rvalid),
        .axi_rready          (shadow_ace_rready),

        .irq_ext             (irq_ext[63:32]),
        .irq_out             (irq_out[1]),
        .timer_clken         (timer_clken[1]),

        .dbg_trig_in         (dbg_trig_in[1]),
        .dbg_trig_out        (dbg_trig_out[1]),
        .trace_out           (trace_out[15:8]),
        .trace_valid         (),

        .clk_active          (shadow_clk_active),
        .pwr_ok              (shadow_pwr_ok),
        .wfi                 (shadow_wfi),
        .wfe                 (shadow_wfe),
        .reset_req           (shadow_reset_req),

        .pwr_req             (pwr_req[1]),
        .pwr_ack             (pwr_ack[1]),
        .pwr_status          (pwr_status[1]),

        .error_out           (),
        .error_valid         (),

        .sec_req             (sec_req[1]),
        .sec_ack             (sec_ack[1]),
        .sec_key             (sec_key),

        .core_id             (ID_SHADOW),

        .result_a            (shadow_result_a),
        .result_b            (shadow_result_b),
        .store_data_valid    (shadow_store_data_valid),
        .store_data          (shadow_store_data),
        .store_addr_valid    (shadow_store_addr_valid),
        .store_addr          (shadow_store_addr)
    );

    //===========================================
    // Lockstep Comparator
    //===========================================
    lockstep_comparator u_comparator (
        .clk                 (clk_pclk),
        .rst_n               (rst_n_poresetn),

        .primary_result_a    (primary_result_a),
        .primary_result_b    (primary_result_b),
        .shadow_result_a     (shadow_result_a),
        .shadow_result_b     (shadow_result_b),

        .primary_store_valid (primary_store_data_valid),
        .shadow_store_valid  (shadow_store_data_valid),
        .primary_store_data  (primary_store_data),
        .shadow_store_data   (shadow_store_data),

        .primary_addr_valid  (primary_store_addr_valid),
        .shadow_addr_valid   (shadow_store_addr_valid),
        .primary_addr        (primary_store_addr),
        .shadow_addr         (shadow_store_addr),

        .error               (compare_error),
        .error_type          (compare_error_type),

        .safety_response     ()
    );

    //===========================================
    // Error Register
    //===========================================
    always @(posedge clk_pclk or negedge rst_n_poresetn) begin
        if (!rst_n_poresetn) begin
            lockstep_error_reg       <= 1'b0;
            lockstep_error_code_reg  <= 32'h0;
        end else begin
            if (compare_error) begin
                lockstep_error_reg       <= 1'b1;
                lockstep_error_code_reg  <= {24'h0, compare_error_type, 2'b00};
            end
        end
    end

    assign lockstep_error      = lockstep_error_reg;
    assign lockstep_error_code = lockstep_error_code_reg;

    //===========================================
    // Output Assignments
    //===========================================
    assign axi_awid     = {shadow_ace_awid[3:0], primary_ace_awid[3:0]};
    assign axi_awaddr   = {shadow_ace_awaddr, primary_ace_awaddr};
    assign axi_awlen    = {shadow_ace_awlen, primary_ace_awlen};
    assign axi_awsize   = {shadow_ace_awsize, primary_ace_awsize};
    assign axi_awburst  = {shadow_ace_awburst, primary_ace_awburst};
    assign axi_awlock   = {shadow_ace_awlock, primary_ace_awlock};
    assign axi_awcache  = {shadow_ace_awcache, primary_ace_awcache};
    assign axi_awprot   = {6'd0};
    assign axi_awqos    = {shadow_ace_awqos, primary_ace_awqos};
    assign axi_awvalid  = {shadow_ace_awvalid, primary_ace_awvalid};
    assign axi_awready  = {shadow_ace_awready, primary_ace_awready};

    assign axi_wdata    = {shadow_ace_wdata, primary_ace_wdata};
    assign axi_wstrb    = {shadow_ace_wstrb, primary_ace_wstrb};
    assign axi_wlast    = {shadow_ace_wlast, primary_ace_wlast};
    assign axi_wvalid   = {shadow_ace_wvalid, primary_ace_wvalid};
    assign axi_wready   = {shadow_ace_wready, primary_ace_wready};

    assign axi_bresp    = {shadow_ace_bresp, primary_ace_bresp};
    assign axi_bvalid   = {shadow_ace_bvalid, primary_ace_bvalid};
    assign axi_bready   = {shadow_ace_bready, primary_ace_bready};

    assign axi_arid     = {shadow_ace_arid[3:0], primary_ace_arid[3:0]};
    assign axi_araddr   = {shadow_ace_araddr, primary_ace_araddr};
    assign axi_arlen    = {shadow_ace_arlen, primary_ace_arlen};
    assign axi_arsize   = {shadow_ace_arsize, primary_ace_arsize};
    assign axi_arburst  = {shadow_ace_arburst, primary_ace_arburst};
    assign axi_arlock   = {shadow_ace_arlock, primary_ace_arlock};
    assign axi_arcache  = {shadow_ace_arcache, primary_ace_arcache};
    assign axi_arprot   = {6'd0};
    assign axi_arqos    = {shadow_ace_arqos, primary_ace_arqos};
    assign axi_arvalid  = {shadow_ace_arvalid, primary_ace_arvalid};
    assign axi_arready  = {shadow_ace_arready, primary_ace_arready};

    assign axi_rdata    = {shadow_ace_rdata, primary_ace_rdata};
    assign axi_rresp    = {shadow_ace_rresp, primary_ace_rresp};
    assign axi_rlast    = {shadow_ace_rlast, primary_ace_rlast};
    assign axi_rvalid   = {shadow_ace_rvalid, primary_ace_rvalid};
    assign axi_rready   = {shadow_ace_rready, primary_ace_rready};

    assign mbist_done   = 1'b1;
    assign error_out    = {lockstep_error_code, 32'h0};
    assign error_valid  = lockstep_error;

endmodule

//===========================================
// Cortex-R52 Single Core Wrapper
//===========================================
module cortex_r52_core (
    input  wire                     clk_pclk,
    input  wire                     clk_sclk,
    input  wire                     rst_n_poresetn,
    input  wire                     rst_n_coresetn,
    input  wire                     scan_enable,
    input  wire                     scan_clk,
    input  wire                     mbist_enable,
    output wire                     mbist_done,
    output wire                     mbist_fail,

    output wire [3:0]               axi_awid,
    output wire [47:0]              axi_awaddr,
    output wire [7:0]               axi_awlen,
    output wire [2:0]               axi_awsize,
    output wire [1:0]               axi_awburst,
    output wire                     axi_awlock,
    output wire [3:0]               axi_awcache,
    output wire [2:0]               axi_awprot,
    output wire [3:0]               axi_awqos,
    output wire                     axi_awvalid,
    input  wire                     axi_awready,

    output wire [255:0]             axi_wdata,
    output wire [31:0]              axi_wstrb,
    output wire                     axi_wlast,
    output wire                     axi_wvalid,
    input  wire                     axi_wready,

    input  wire [1:0]               axi_bresp,
    input  wire                     axi_bvalid,
    output wire                     axi_bready,

    output wire [3:0]               axi_arid,
    output wire [47:0]              axi_araddr,
    output wire [7:0]               axi_arlen,
    output wire [2:0]               axi_arsize,
    output wire [1:0]               axi_arburst,
    output wire                     axi_arlock,
    output wire [3:0]               axi_arcache,
    output wire [2:0]               axi_arprot,
    output wire [3:0]               axi_arqos,
    output wire                     axi_arvalid,
    input  wire                     axi_arready,

    input  wire [255:0]             axi_rdata,
    input  wire [1:0]               axi_rresp,
    input  wire                     axi_rlast,
    input  wire                     axi_rvalid,
    output wire                     axi_rready,

    input  wire [31:0]              irq_ext,
    output wire                     irq_out,
    output wire                     timer_clken,

    input  wire                     dbg_trig_in,
    output wire                     dbg_trig_out,
    output wire [7:0]               trace_out,
    output wire                     trace_valid,

    output wire                     clk_active,
    output wire                     pwr_ok,
    output wire                     wfi,
    output wire                     wfe,
    output wire                     reset_req,

    input  wire                     pwr_req,
    output wire                     pwr_ack,
    output wire [7:0]               pwr_status,

    output wire [31:0]              error_out,
    output wire                     error_valid,

    input  wire                     sec_req,
    output wire                     sec_ack,
    input  wire [127:0]             sec_key,

    input  wire [3:0]               core_id,

    output wire [31:0]              result_a,
    output wire [31:0]              result_b,
    output wire                     store_data_valid,
    output wire [255:0]             store_data,
    output wire                     store_addr_valid,
    output wire [47:0]              store_addr
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
    assign mbist_done    = 1'b1;
    assign mbist_fail    = 1'b0;
    assign dbg_trig_out  = dbg_trig_in;
    assign trace_valid   = 1'b0;

    assign axi_awid      = 4'h0;
    assign axi_awaddr    = 48'h0;
    assign axi_awlen     = 8'h0;
    assign axi_awsize    = 3'd5;
    assign axi_awburst   = 2'b01;
    assign axi_awlock    = 1'b0;
    assign axi_awcache   = 4'b0011;
    assign axi_awprot    = 3'd0;
    assign axi_awqos     = 4'h0;
    assign axi_awvalid   = 1'b0;
    assign axi_bready    = 1'b1;
    assign axi_wdata     = 256'h0;
    assign axi_wstrb     = 32'h0;
    assign axi_wlast     = 1'b0;
    assign axi_wvalid    = 1'b0;

    assign axi_arid      = 4'h0;
    assign axi_araddr    = 48'h0;
    assign axi_arlen     = 8'h0;
    assign axi_arsize    = 3'd5;
    assign axi_arburst   = 2'b01;
    assign axi_arlock    = 1'b0;
    assign axi_arcache   = 4'b0011;
    assign axi_arprot    = 3'd0;
    assign axi_arqos     = 4'h0;
    assign axi_arvalid   = 1'b0;
    assign axi_rready    = 1'b1;

    assign trace_out     = 8'h0;
    assign irq_out       = irq_ext[0];
    assign error_out     = 32'h0;
    assign error_valid   = 1'b0;

    assign result_a      = 32'h0;
    assign result_b      = 32'h0;
    assign store_data_valid = 1'b0;
    assign store_data    = 256'h0;
    assign store_addr_valid = 1'b0;
    assign store_addr    = 48'h0;

endmodule

//===========================================
// Lockstep Comparator
//===========================================
module lockstep_comparator (
    input  wire            clk,
    input  wire            rst_n,

    input  wire [31:0]     primary_result_a,
    input  wire [31:0]     primary_result_b,
    input  wire [31:0]     shadow_result_a,
    input  wire [31:0]     shadow_result_b,

    input  wire            primary_store_valid,
    input  wire            shadow_store_valid,
    input  wire [255:0]    primary_store_data,
    input  wire [255:0]    shadow_store_data,

    input  wire            primary_addr_valid,
    input  wire            shadow_addr_valid,
    input  wire [47:0]     primary_addr,
    input  wire [47:0]     shadow_addr,

    output wire            error,
    output wire [5:0]      error_type,

    output wire            safety_response
);

    wire result_a_mismatch = (primary_result_a != shadow_result_a);
    wire result_b_mismatch = (primary_result_b != shadow_result_b);
    wire store_data_mismatch;
    wire store_addr_mismatch;

    assign store_data_mismatch = (primary_store_data != shadow_store_data);
    assign store_addr_mismatch = (primary_addr != shadow_addr);

    assign error       = result_a_mismatch | result_b_mismatch | store_data_mismatch | store_addr_mismatch;
    assign error_type  = {result_a_mismatch, result_b_mismatch, store_data_mismatch, store_addr_mismatch, 2'b00};
    assign safety_response = error;

endmodule

endmodule
