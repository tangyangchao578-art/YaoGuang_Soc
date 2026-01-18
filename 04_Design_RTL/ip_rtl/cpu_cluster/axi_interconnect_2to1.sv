// Copyright (c) 2026 YaoGuang SoC Project
// All rights reserved

// Module: axi_interconnect_2to1
// Description: 2-to-1 AXI4 Interconnect for R52 Cluster
// Version: 1.0
// Author: Frontend Design Engineer
// Date: 2026-01-19

`timescale 1ns/1ps

module axi_interconnect_2to1 (
    //===========================================
    // Clock and Reset
    //===========================================
    input  wire            clk,
    input  wire            rst_n,

    //===========================================
    // Slave Interface (2 masters: Core0, Core1)
    //===========================================
    input  wire [2*4-1:0]      s_awid,
    input  wire [2*48-1:0]     s_awaddr,
    input  wire [2*8-1:0]      s_awlen,
    input  wire [2*3-1:0]      s_awsize,
    input  wire [2*2-1:0]      s_awburst,
    input  wire [2-1:0]        s_awlock,
    input  wire [2*4-1:0]      s_awcache,
    input  wire [2*3-1:0]      s_awprot,
    input  wire [2*4-1:0]      s_awqos,
    input  wire [2-1:0]        s_awvalid,
    output wire [2-1:0]        s_awready,

    input  wire [2*256-1:0]    s_wdata,
    input  wire [2*32-1:0]     s_wstrb,
    input  wire [2-1:0]        s_wlast,
    input  wire [2-1:0]        s_wvalid,
    output wire [2-1:0]        s_wready,

    output wire [2*2-1:0]      s_bresp,
    output wire [2*4-1:0]      s_bid,
    output wire [2-1:0]        s_bvalid,
    input  wire [2-1:0]        s_bready,

    input  wire [2*4-1:0]      s_arid,
    input  wire [2*48-1:0]     s_araddr,
    input  wire [2*8-1:0]      s_arlen,
    input  wire [2*3-1:0]      s_arsize,
    input  wire [2*2-1:0]      s_arburst,
    input  wire [2-1:0]        s_arlock,
    input  wire [2*4-1:0]      s_arcache,
    input  wire [2*3-1:0]      s_arprot,
    input  wire [2*4-1:0]      s_arqos,
    input  wire [2-1:0]        s_arvalid,
    output wire [2-1:0]        s_arready,

    output wire [2*256-1:0]    s_rdata,
    output wire [2*2-1:0]      s_rresp,
    output wire [2*4-1:0]      s_rid,
    output wire [2-1:0]        s_rlast,
    output wire [2-1:0]        s_rvalid,
    input  wire [2-1:0]        s_rready,

    //===========================================
    // Master Interface (1 target: NoC)
    //===========================================
    output wire [3:0]          m_awid,
    output wire [47:0]         m_awaddr,
    output wire [7:0]          m_awlen,
    output wire [2:0]          m_awsize,
    output wire [1:0]          m_awburst,
    output wire                m_awlock,
    output wire [3:0]          m_awcache,
    output wire [2:0]          m_awprot,
    output wire [3:0]          m_awqos,
    output wire                m_awvalid,
    input  wire                m_awready,

    output wire [255:0]        m_wdata,
    output wire [31:0]         m_wstrb,
    output wire                m_wlast,
    output wire                m_wvalid,
    input  wire                m_wready,

    input  wire [1:0]          m_bresp,
    input  wire [3:0]          m_bid,
    input  wire                m_bvalid,
    output wire                m_bready,

    output wire [3:0]          m_arid,
    output wire [47:0]         m_araddr,
    output wire [7:0]          m_arlen,
    output wire [2:0]          m_arsize,
    output wire [1:0]          m_arburst,
    output wire                m_arlock,
    output wire [3:0]          m_arcache,
    output wire [2:0]          m_arprot,
    output wire [3:0]          m_arqos,
    output wire                m_arvalid,
    input  wire                m_arready,

    input  wire [255:0]        m_rdata,
    input  wire [1:0]          m_rresp,
    input  wire [3:0]          m_rid,
    input  wire                m_rlast,
    input  wire                m_rvalid,
    output wire                m_rready
);

    //===========================================
    // Parameters
    //===========================================
    parameter NUM_SLAVES = 2;
    parameter ID_WIDTH = 4;
    parameter ADDR_WIDTH = 48;
    parameter DATA_WIDTH = 256;

    //===========================================
    // Arbitration Signals
    //===========================================
    wire [NUM_SLAVES-1:0]      aw_request;
    wire [NUM_SLAVES-1:0]      aw_grant;
    wire [NUM_SLAVES-1:0]      ar_request;
    wire [NUM_SLAVES-1:0]      ar_grant;

    reg                         aw_arbiter;
    reg                         ar_arbiter;

    wire                       aw_active;
    wire                       ar_active;

    //===========================================
    // Write Address Channel Arbitration
    //===========================================
    assign aw_request = s_awvalid;
    assign aw_active  = |aw_request;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            aw_arbiter <= 1'd0;
        end else begin
            if (aw_active) begin
                aw_arbiter <= ~aw_arbiter;
            end
        end
    end

    fixed_prio_arbiter #(
        .NUM_MASTERS(NUM_SLAVES)
    ) u_aw_arbiter (
        .request        (aw_request),
        .priority       (aw_arbiter),
        .grant          (aw_grant)
    );

    //===========================================
    // Read Address Channel Arbitration
    //===========================================
    assign ar_request = s_arvalid;
    assign ar_active  = |ar_request;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ar_arbiter <= 1'd0;
        end else begin
            if (ar_active) begin
                ar_arbiter <= ~ar_arbiter;
            end
        end
    end

    fixed_prio_arbiter #(
        .NUM_MASTERS(NUM_SLAVES)
    ) u_ar_arbiter (
        .request        (ar_request),
        .priority       (ar_arbiter),
        .grant          (ar_grant)
    );

    //===========================================
    // Master Selection
    //===========================================
    wire aw_master = aw_grant[1] ? 1'd1 : 1'd0;
    wire ar_master = ar_grant[1] ? 1'd1 : 1'd0;

    //===========================================
    // Write Path (Slave -> Master)
    //===========================================
    assign m_awid     = s_awid[aw_master*4 +: 4];
    assign m_awaddr   = s_awaddr[aw_master*48 +: 48];
    assign m_awlen    = s_awlen[aw_master*8 +: 8];
    assign m_awsize   = s_awsize[aw_master*3 +: 3];
    assign m_awburst  = s_awburst[aw_master*2 +: 2];
    assign m_awlock   = s_awlock[aw_master];
    assign m_awcache  = s_awcache[aw_master*4 +: 4];
    assign m_awprot   = s_awprot[aw_master*3 +: 3];
    assign m_awqos    = s_awqos[aw_master*4 +: 4];
    assign m_awvalid  = |aw_grant;
    assign s_awready  = aw_grant & {NUM_SLAVES{m_awready}};

    assign m_wdata    = s_wdata[aw_master*256 +: 256];
    assign m_wstrb    = s_wstrb[aw_master*32 +: 32];
    assign m_wlast    = s_wlast[aw_master];
    assign m_wvalid   = |aw_grant & s_wvalid[aw_master];
    assign s_wready   = aw_grant & {NUM_SLAVES{m_wready}};

    //===========================================
    // Read Path (Slave -> Master)
    //===========================================
    assign m_arid     = s_arid[ar_master*4 +: 4];
    assign m_araddr   = s_araddr[ar_master*48 +: 48];
    assign m_arlen    = s_arlen[ar_master*8 +: 8];
    assign m_arsize   = s_arsize[ar_master*3 +: 3];
    assign m_arburst  = s_arburst[ar_master*2 +: 2];
    assign m_arlock   = s_arlock[ar_master];
    assign m_arcache  = s_arcache[ar_master*4 +: 4];
    assign m_arprot   = s_arprot[ar_master*3 +: 3];
    assign m_arqos    = s_arqos[ar_master*4 +: 4];
    assign m_arvalid  = |ar_grant;
    assign s_arready  = ar_grant & {NUM_SLAVES{m_arready}};

    //===========================================
    // Response Path (Master -> Slave)
    //===========================================
    reg [NUM_SLAVES-1:0]       b_router;
    always @(*) begin
        b_router = 2'd0;
        if (m_bvalid) begin
            b_router[m_bid[0]] = 1'b1;
        end
    end

    assign s_bresp   = {NUM_SLAVES{m_bresp}};
    assign s_bid     = {NUM_SLAVES{m_bid}};
    assign s_bvalid  = b_router & {NUM_SLAVES{m_bvalid}};
    assign m_bready  = |b_router;

    //===========================================
    // Read Response Path (Master -> Slave)
    //===========================================
    reg [NUM_SLAVES-1:0]       r_router;
    always @(*) begin
        r_router = 2'd0;
        if (m_rvalid) begin
            r_router[m_rid[0]] = 1'b1;
        end
    end

    assign s_rdata   = {NUM_SLAVES{m_rdata}};
    assign s_rresp   = {NUM_SLAVES{m_rresp}};
    assign s_rid     = {NUM_SLAVES{m_rid}};
    assign s_rlast   = r_router & {NUM_SLAVES{m_rlast}};
    assign s_rvalid  = r_router & {NUM_SLAVES{m_rvalid}};
    assign m_rready  = |r_router;

endmodule

//===========================================
// Fixed Priority Arbiter
//===========================================
module fixed_prio_arbiter #(
    parameter NUM_MASTERS = 2
) (
    input  wire [NUM_MASTERS-1:0]      request,
    input  wire                        priority,
    output wire [NUM_MASTERS-1:0]      grant
);

    if (NUM_MASTERS == 2) begin
        assign grant[1] = request[1] & (~request[0] | priority);
        assign grant[0] = request[0] & (~request[1] | ~priority);
    end else begin
        assign grant = request;
    end

endmodule

endmodule
