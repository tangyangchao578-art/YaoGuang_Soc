// Copyright (c) 2026 YaoGuang SoC Project
// All rights reserved

// Module: ace_interconnect_8to1
// Description: 8-to-1 ACE4 Interconnect for A78AE Cluster
// Version: 1.0
// Author: Frontend Design Engineer
// Date: 2026-01-19

`timescale 1ns/1ps

module ace_interconnect_8to1 (
    //===========================================
    // Clock and Reset
    //===========================================
    input  wire            clk,
    input  wire            rst_n,

    //===========================================
    // Core Interface (8 cores)
    //===========================================
    input  wire [8*512-1:0]    core_awid,
    input  wire [8*48-1:0]     core_awaddr,
    input  wire [8*8-1:0]      core_awlen,
    input  wire [8*2-1:0]      core_awburst,
    input  wire [8-1:0]        core_awlock,
    input  wire [8*4-1:0]      core_awcache,
    input  wire [8*4-1:0]      core_awqos,
    input  wire [8-1:0]        core_awvalid,
    output wire [8-1:0]        core_awready,

    input  wire [8*512-1:0]    core_wdata,
    input  wire [8*64-1:0]     core_wstrb,
    input  wire [8-1:0]        core_wlast,
    input  wire [8-1:0]        core_wvalid,
    output wire [8-1:0]        core_wready,

    output wire [8*2-1:0]      core_bresp,
    output wire [8-1:0]        core_bvalid,
    input  wire [8-1:0]        core_bready,

    input  wire [8*512-1:0]    core_arid,
    input  wire [8*48-1:0]     core_araddr,
    input  wire [8*8-1:0]      core_arlen,
    input  wire [8*2-1:0]      core_arburst,
    input  wire [8-1:0]        core_arlock,
    input  wire [8*4-1:0]      core_arcache,
    input  wire [8*4-1:0]      core_arqos,
    input  wire [8-1:0]        core_arvalid,
    output wire [8-1:0]        core_arready,

    output wire [8*512-1:0]    core_rdata,
    output wire [8*2-1:0]      core_rresp,
    output wire [8-1:0]        core_rlast,
    output wire [8-1:0]        core_rvalid,
    input  wire [8-1:0]        core_rready,

    //===========================================
    // NoC Interface (1 master)
    //===========================================
    output wire [511:0]        noc_awid,
    output wire [47:0]         noc_awaddr,
    output wire [7:0]          noc_awlen,
    output wire [2:0]          noc_awsize,
    output wire [1:0]          noc_awburst,
    output wire                noc_awlock,
    output wire [3:0]          noc_awcache,
    output wire [2:0]          noc_awprot,
    output wire [3:0]          noc_awqos,
    output wire [5:0]          noc_awregion,
    output wire [4:0]          noc_awuser,
    output wire                noc_awvalid,
    input  wire                noc_awready,

    output wire [511:0]        noc_wdata,
    output wire [63:0]         noc_wstrb,
    output wire                noc_wlast,
    output wire [4:0]          noc_wuser,
    output wire                noc_wvalid,
    input  wire                noc_wready,

    input  wire [1:0]          noc_bresp,
    input  wire [5:0]          noc_bid,
    input  wire [4:0]          noc_buser,
    input  wire                noc_bvalid,
    output wire                noc_bready,

    output wire [511:0]        noc_arid,
    output wire [47:0]         noc_araddr,
    output wire [7:0]          noc_arlen,
    output wire [2:0]          noc_arsize,
    output wire [1:0]          noc_arburst,
    output wire                noc_arlock,
    output wire [3:0]          noc_arcache,
    output wire [2:0]          noc_arprot,
    output wire [3:0]          noc_arqos,
    output wire [5:0]          noc_arregion,
    output wire [4:0]          noc_aruser,
    output wire                noc_arvalid,
    input  wire                noc_arready,

    input  wire [511:0]        noc_rdata,
    input  wire [1:0]          noc_rresp,
    input  wire [5:0]          noc_rid,
    input  wire                noc_rlast,
    input  wire [4:0]          noc_ruser,
    input  wire                noc_rvalid,
    output wire                noc_rready,

    //===========================================
    // Snoop Interface
    //===========================================
    input  wire [3:0]          noc_awsnoop,
    input  wire [4:0]          noc_awdomain,
    input  wire                noc_awparity,
    output wire [3:0]          noc_acsnoop,
    output wire [4:0]          noc_acdomain,
    output wire                noc_acparity,

    input  wire [1:0]          noc_crresp,
    input  wire [5:0]          noc_crid,
    input  wire                noc_crvalid,
    output wire                noc_crready,

    output wire [511:0]        noc_cddata,
    output wire [63:0]         noc_cdwstrb,
    output wire                noc_cdlast,
    output wire                noc_cdvalid,
    input  wire                noc_cdready
);

    //===========================================
    // Parameters
    //===========================================
    parameter NUM_MASTERS = 8;
    parameter ID_WIDTH = 6;
    parameter ADDR_WIDTH = 48;
    parameter DATA_WIDTH = 512;

    //===========================================
    // Arbitration Signals
    //===========================================
    wire [NUM_MASTERS-1:0]     aw_request;
    wire [NUM_MASTERS-1:0]     aw_grant;
    wire [NUM_MASTERS-1:0]     ar_request;
    wire [NUM_MASTERS-1:0]     ar_grant;

    reg [2:0]                  aw_arbiter;
    reg [2:0]                  ar_arbiter;

    wire                       aw_active;
    wire                       ar_active;

    //===========================================
    // Write Address Channel Arbitration
    //===========================================
    assign aw_request = core_awvalid;
    assign aw_active  = |aw_request;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            aw_arbiter <= 3'd0;
        end else begin
            if (aw_active) begin
                aw_arbiter <= aw_arbiter + 1;
            end
        end
    end

    round_robin_arbiter #(
        .NUM_MASTERS(NUM_MASTERS)
    ) u_aw_arbiter (
        .clk            (clk),
        .rst_n          (rst_n),
        .request        (aw_request),
        .priority       (aw_arbiter),
        .grant          (aw_grant)
    );

    //===========================================
    // Read Address Channel Arbitration
    //===========================================
    assign ar_request = core_arvalid;
    assign ar_active  = |ar_request;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ar_arbiter <= 3'd0;
        end else begin
            if (ar_active) begin
                ar_arbiter <= ar_arbiter + 1;
            end
        end
    end

    round_robin_arbiter #(
        .NUM_MASTERS(NUM_MASTERS)
    ) u_ar_arbiter (
        .clk            (clk),
        .rst_n          (rst_n),
        .request        (ar_request),
        .priority       (ar_arbiter),
        .grant          (ar_grant)
    );

    //===========================================
    // Master Selection
    //===========================================
    wire [$clog2(NUM_MASTERS)-1:0] aw_master;
    wire [$clog2(NUM_MASTERS)-1:0] ar_master;

    onehot_to_binary #(
        .WIDTH(NUM_MASTERS)
    ) u_aw_master (
        .onehot         (aw_grant),
        .binary         (aw_master)
    );

    onehot_to_binary #(
        .WIDTH(NUM_MASTERS)
    ) u_ar_master (
        .onehot         (ar_grant),
        .binary         (ar_master)
    );

    //===========================================
    // Write Path (Core -> NoC)
    //===========================================
    assign noc_awid     = core_awid[aw_master*512 +: 512];
    assign noc_awaddr   = core_awaddr[aw_master*48 +: 48];
    assign noc_awlen    = core_awlen[aw_master*8 +: 8];
    assign noc_awburst  = core_awburst[aw_master*2 +: 2];
    assign noc_awlock   = core_awlock[aw_master];
    assign noc_awcache  = core_awcache[aw_master*4 +: 4];
    assign noc_awqos    = core_awqos[aw_master*4 +: 4];
    assign noc_awregion = {3'd0, aw_master};
    assign noc_awuser   = 5'd0;
    assign noc_awvalid  = |aw_grant;
    assign core_awready = aw_grant & {NUM_MASTERS{noc_awready}};

    assign noc_wdata    = core_wdata[aw_master*512 +: 512];
    assign noc_wstrb    = core_wstrb[aw_master*64 +: 64];
    assign noc_wlast    = core_wlast[aw_master];
    assign noc_wuser    = 5'd0;
    assign noc_wvalid   = |aw_grant & core_wvalid[aw_master];
    assign core_wready  = aw_grant & {NUM_MASTERS{noc_wready}};

    //===========================================
    // Read Path (Core -> NoC)
    //===========================================
    assign noc_arid     = core_arid[ar_master*512 +: 512];
    assign noc_araddr   = core_araddr[ar_master*48 +: 48];
    assign noc_arlen    = core_arlen[ar_master*8 +: 8];
    assign noc_arburst  = core_arburst[ar_master*2 +: 2];
    assign noc_arlock   = core_arlock[ar_master];
    assign noc_arcache  = core_arcache[ar_master*4 +: 4];
    assign noc_arqos    = core_arqos[ar_master*4 +: 4];
    assign noc_arregion = {3'd0, ar_master};
    assign noc_aruser   = 5'd0;
    assign noc_arvalid  = |ar_grant;
    assign core_arready = ar_grant & {NUM_MASTERS{noc_arready}};

    //===========================================
    // Response Path (NoC -> Core)
    //===========================================
    // Write response routing
    reg [NUM_MASTERS-1:0]       b_router;
    always @(*) begin
        b_router = 8'd0;
        if (noc_bvalid) begin
            b_router[noc_bid[2:0]] = 1'b1;
        end
    end

    assign core_bresp   = {NUM_MASTERS{noc_bresp}};
    assign core_bvalid  = b_router & {NUM_MASTERS{noc_bvalid}};
    assign noc_bready   = |b_router;

    // Read response routing
    reg [NUM_MASTERS-1:0]       r_router;
    always @(*) begin
        r_router = 8'd0;
        if (noc_rvalid) begin
            r_router[noc_rid[2:0]] = 1'b1;
        end
    end

    assign core_rdata   = {NUM_MASTERS{noc_rdata}};
    assign core_rresp   = {NUM_MASTERS{noc_rresp}};
    assign core_rlast   = r_router & {NUM_MASTERS{noc_rlast}};
    assign core_rvalid  = r_router & {NUM_MASTERS{noc_rvalid}};
    assign noc_rready   = |r_router;

    //===========================================
    // Snoop Passthrough
    //===========================================
    assign noc_acsnoop  = noc_awsnoop;
    assign noc_acdomain = noc_awdomain;
    assign noc_acparity = noc_awparity;

    assign noc_crready  = 1'b1;
    assign noc_cddata   = 512'h0;
    assign noc_cdwstrb  = 64'h0;
    assign noc_cdlast   = 1'b0;
    assign noc_cdvalid  = 1'b0;

endmodule

//===========================================
// Round Robin Arbiter
//===========================================
module round_robin_arbiter #(
    parameter NUM_MASTERS = 8
) (
    input  wire                        clk,
    input  wire                        rst_n,
    input  wire [NUM_MASTERS-1:0]      request,
    input  wire [$clog2(NUM_MASTERS)-1:0] priority,
    output wire [NUM_MASTERS-1:0]      grant
);

    wire [NUM_MASTERS-1:0] masked_request = request & ~({NUM_MASTERS{1'b1}} << priority);

    assign grant = masked_request ? masked_request : request;

endmodule

//===========================================
// One-Hot to Binary Encoder
//===========================================
module onehot_to_binary #(
    parameter WIDTH = 8
) (
    input  wire [WIDTH-1:0]    onehot,
    output wire [$clog2(WIDTH)-1:0] binary
);

    integer i;
    reg [$clog2(WIDTH)-1:0] binary_reg;

    always @(*) begin
        binary_reg = 0;
        for (i = 0; i < WIDTH; i = i + 1) begin
            if (onehot[i]) begin
                binary_reg = i[$clog2(WIDTH)-1:0];
            end
        end
    end

    assign binary = binary_reg;

endmodule

endmodule
