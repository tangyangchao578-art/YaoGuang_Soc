// Copyright (c) 0 YaoGuang SoC Project
// All rights reserved

// Module: l2_cache_a78ae
// Description: A78AE L2 Cache (512KB per core, 8-way set associative)
// Version: 1.0
// Author: Frontend Design Engineer
// Date: 2026-01-19

`timescale 1ns/1ps

module l2_cache_a78ae #(
    parameter DATA_WIDTH = 512,
    parameter TAG_WIDTH  = 40,
    parameter INDEX_WIDTH= 8,
    parameter OFFSET_WIDTH=6,
    parameter NUM_WAYS   = 8,
    parameter NUM_SETS   = 256,
    parameter CACHE_SIZE = 512 * 1024
) (
    //===========================================
    // Clock and Reset
    //===========================================
    input  wire                     clk,
    input  wire                     rst_n,
    input  wire                     clk_early,

    //===========================================
    // Core Interface
    //===========================================
    input  wire [47:0]              core_addr,
    input  wire                     core_read,
    input  wire                     core_write,
    input  wire [DATA_WIDTH-1:0]    core_wdata,
    input  wire [DATA_WIDTH/8-1:0]  core_wstrb,
    input  wire                     core_burst,
    input  wire [7:0]               core_len,
    input  wire [2:0]               core_size,
    output wire [DATA_WIDTH-1:0]    core_rdata,
    output wire [1:0]               core_rresp,
    output wire                     core_rvalid,
    output wire                     core_rlast,
    output wire [1:0]               core_bresp,
    output wire                     core_bvalid,
    input  wire                     core_ready,

    //===========================================
    // ACE4 Interface
    //===========================================
    output wire [511:0]             ace_awid,
    output wire [47:0]              ace_awaddr,
    output wire [7:0]               ace_awlen,
    output wire [2:0]               ace_awsize,
    output wire [1:0]               ace_awburst,
    output wire                     ace_awlock,
    output wire [3:0]               ace_awcache,
    output wire [2:0]               ace_awprot,
    output wire [3:0]               ace_awqos,
    output wire                     ace_awvalid,
    input  wire                     ace_awready,

    output wire [511:0]             ace_wdata,
    output wire [63:0]              ace_wstrb,
    output wire                     ace_wlast,
    output wire [4:0]               ace_wuser,
    output wire                     ace_wvalid,
    input  wire                     ace_wready,

    input  wire [1:0]               ace_bresp,
    input  wire [5:0]               ace_bid,
    input  wire [4:0]               ace_buser,
    input  wire                     ace_bvalid,
    output wire                     ace_bready,

    output wire [511:0]             ace_arid,
    output wire [47:0]              ace_araddr,
    output wire [7:0]               ace_arlen,
    output wire [2:0]               ace_arsize,
    output wire [1:0]               ace_arburst,
    output wire                     ace_arlock,
    output wire [3:0]               ace_arcache,
    output wire [2:0]               ace_arprot,
    output wire [3:0]               ace_arqos,
    output wire                     ace_arvalid,
    input  wire                     ace_arready,

    input  wire [511:0]             ace_rdata,
    input  wire [1:0]               ace_rresp,
    input  wire [5:0]               ace_rid,
    input  wire                     ace_rlast,
    input  wire [4:0]               ace_ruser,
    input  wire                     ace_rvalid,
    output wire                     ace_rready,

    //===========================================
    // Snoop Interface
    //===========================================
    input  wire [3:0]               ace_acsnoop,
    input  wire [4:0]               ace_acdomain,
    input  wire                     ace_acparity,
    output wire [3:0]               ace_crresp,
    output wire [5:0]               ace_crid,
    output wire                     ace_crvalid,
    input  wire                     ace_crready,

    output wire [511:0]             ace_cddata,
    output wire [63:0]              ace_cdwstrb,
    output wire                     ace_cdlast,
    output wire                     ace_cdvalid,
    input  wire                     ace_cdready,

    //===========================================
    // Control Interface
    //===========================================
    input  wire [31:0]              l2_ctrl,
    output wire                     l2_ready,
    output wire                     l2_parity_err,
    input  wire                     l2_bypass,
    input  wire                     l2_power_down,
    input  wire                     l2_flush,
    input  wire                     l2_inv,

    //===========================================
    // Performance Interface
    //===========================================
    output wire [31:0]              perf_hit_count,
    output wire [31:0]              perf_miss_count,
    output wire [31:0]              perf_evict_count
);

    //===========================================
    // Parameters
    //===========================================
    localparam BYTE_WIDTH = 8;
    localparam WORDS_PER_LINE = DATA_WIDTH / 64;

    //===========================================
    // Internal Signals
    //===========================================
    wire [INDEX_WIDTH-1:0]          index;
    wire [TAG_WIDTH-1:0]            tag;
    wire [OFFSET_WIDTH-1:0]         offset;
    wire [NUM_WAYS-1:0]             way_hit;
    wire [NUM_WAYS-1:0]             way_replace;
    wire [NUM_WAYS-1:0]             way_valid;

    wire [DATA_WIDTH-1:0]           data_rdata;
    wire [DATA_WIDTH-1:0]           data_wdata;
    wire [DATA_WIDTH-1:0]           line_wdata;
    wire [NUM_WAYS*DATA_WIDTH-1:0]  data_array;
    wire [NUM_WAYS*TAG_WIDTH-1:0]   tag_array;
    wire [NUM_WAYS-1:0]             valid_array;
    wire [NUM_WAYS-1:0]             dirty_array;
    wire [NUM_WAYS-1:0]             lru_array;

    reg                             state_idle;
    reg                             state_read;
    reg                             state_write;
    reg                             state_fill;
    reg                             state_evict;
    reg [3:0]                       state_next;

    reg                             req_read;
    reg                             req_write;
    reg [47:0]                      req_addr;
    reg [DATA_WIDTH-1:0]            req_wdata;
    reg [DATA_WIDTH/8-1:0]          req_wstrb;
    reg [7:0]                       req_len;
    reg [2:0]                       req_size;

    wire                            hit;
    wire                            miss;
    wire                            dirty_evict;
    wire [NUM_WAYS-1:0]             hit_way;

    reg [511:0]                     ace_rdata_reg;
    reg                             ace_rvalid_reg;
    reg                             ace_rlast_reg;
    reg [1:0]                       ace_rresp_reg;

    reg [511:0]                     ace_wdata_reg;
    reg                             ace_wvalid_reg;
    reg                             ace_wlast_reg;
    reg [63:0]                      ace_wstrb_reg;

    //===========================================
    // Address Decode
    //===========================================
    assign index  = req_addr[OFFSET_WIDTH +: INDEX_WIDTH];
    assign tag    = req_addr[OFFSET_WIDTH + INDEX_WIDTH +: TAG_WIDTH];
    assign offset = req_addr[OFFSET_WIDTH-1:0];

    //===========================================
    // Tag RAM Instance
    //===========================================
    l2_tag_ram #(
        .WIDTH(TAG_WIDTH),
        .DEPTH(NUM_SETS),
        .NUM_WAYS(NUM_WAYS)
    ) u_tag_ram (
        .clk               (clk),
        .rst_n             (rst_n),

        .index             (index),
        .way_read          (way_hit),
        .tag_read          (tag_array),
        .valid_read        (valid_array),
        .dirty_read        (dirty_array),

        .way_write         (way_replace),
        .tag_write         (hit ? tag : tag),
        .valid_write       (hit ? 1'b1 : 1'b1),
        .dirty_write       (req_write),

        .l2_flush          (l2_flush),
        .l2_inv            (l2_inv)
    );

    //===========================================
    // Data RAM Instance
    //===========================================
    l2_data_ram #(
        .WIDTH(DATA_WIDTH),
        .DEPTH(NUM_SETS),
        .NUM_WAYS(NUM_WAYS)
    ) u_data_ram (
        .clk               (clk),
        .rst_n             (rst_n),

        .index             (index),
        .way_read          (hit_way),
        .data_read         (data_rdata),

        .way_write         (way_replace),
        .data_write        (req_write ? req_wdata : line_wdata),
        .byte_enable       (req_write ? req_wstrb : {DATA_WIDTH/8{1'b1}})
    );

    //===========================================
    // LRU Replacement
    //===========================================
    l2_lru #(
        .NUM_WAYS(NUM_WAYS),
        .NUM_SETS(NUM_SETS)
    ) u_lru (
        .clk               (clk),
        .rst_n             (rst_n),

        .index             (index),
        .hit_way           (hit_way),
        .access_way        (hit ? hit_way : way_replace),

        .lru_update        (hit | miss),
        .lru_read          (lru_array)
    );

    //===========================================
    // Hit Detection
    //===========================================
    genvar i;
    generate
        for (i = 0; i < NUM_WAYS; i = i + 1) begin : HIT_GEN
            assign way_hit[i] = valid_array[i] & (tag_array[i*TAG_WIDTH +: TAG_WIDTH] == tag);
        end
    endgenerate

    assign hit        = |way_hit;
    assign miss       = ~hit;
    assign hit_way    = hit ? way_hit : way_replace;
    assign dirty_evict = |(dirty_array & way_replace);

    //===========================================
    // State Machine
    //===========================================
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state_idle  <= 1'b1;
            state_read  <= 1'b0;
            state_write <= 1'b0;
            state_fill  <= 1'b0;
            state_evict <= 1'b0;
        end else begin
            state_idle  <= (state_next == 4'd0);
            state_read  <= (state_next == 4'd1);
            state_write <= (state_next == 4'd2);
            state_fill  <= (state_next == 4'd3);
            state_evict <= (state_next == 4'd4);
        end
    end

    always @(*) begin
        case ({state_idle, state_read, state_write, state_fill, state_evict})
            5'b10000: begin
                if (core_read | core_write) begin
                    if (hit) begin
                        state_next = core_read ? 4'd1 : 4'd2;
                    end else begin
                        state_next = dirty_evict ? 4'd4 : 4'd3;
                    end
                end else begin
                    state_next = 4'd0;
                end
            end
            5'b01000: begin
                state_next = core_ready ? 4'd0 : 4'd1;
            end
            5'b00100: begin
                state_next = core_ready ? 4'd0 : 4'd2;
            end
            5'b00010: begin
                state_next = ace_rvalid ? 4'd1 : 4'd3;
            end
            5'b00001: begin
                state_next = ace_bvalid ? 4'd3 : 4'd4;
            end
            default: state_next = 4'd0;
        endcase
    end

    //===========================================
    // Request Pipeline
    //===========================================
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            req_read   <= 1'b0;
            req_write  <= 1'b0;
            req_addr   <= 48'h0;
            req_wdata  <= 512'h0;
            req_wstrb  <= 64'h0;
            req_len    <= 8'h0;
            req_size   <= 3'd0;
        end else begin
            if (state_idle & (core_read | core_write)) begin
                req_read   <= core_read;
                req_write  <= core_write;
                req_addr   <= core_addr;
                req_wdata  <= core_wdata;
                req_wstrb  <= core_wstrb;
                req_len    <= core_len;
                req_size   <= core_size;
            end
        end
    end

    //===========================================
    // ACE Read Interface
    //===========================================
    assign ace_arid     = 6'h0;
    assign ace_araddr   = {tag, index, {OFFSET_WIDTH{1'b0}}};
    assign ace_arlen    = 8'd7;
    assign ace_arsize   = 3'd6;
    assign ace_arburst  = 2'b01;
    assign ace_arlock   = 1'b0;
    assign ace_arcache  = 4'b0011;
    assign ace_arprot   = 3'd0;
    assign ace_arqos    = 4'h0;
    assign ace_arvalid  = state_fill;
    assign ace_rready   = 1'b1;

    //===========================================
    // ACE Write Interface
    //===========================================
    assign ace_awid     = 6'h0;
    assign ace_awaddr   = {tag, index, {OFFSET_WIDTH{1'b0}}};
    assign ace_awlen    = 8'd7;
    assign ace_awsize   = 3'd6;
    assign ace_awburst  = 2'b01;
    assign ace_awlock   = 1'b0;
    assign ace_awcache  = 4'b0011;
    assign ace_awprot   = 3'd0;
    assign ace_awqos    = 4'h0;
    assign ace_awvalid  = state_evict;
    assign ace_bready   = 1'b1;

    //===========================================
    // Fill Data Path
    //===========================================
    always @(posedge clk) begin
        if (ace_rvalid) begin
            ace_rdata_reg  <= ace_rdata;
            ace_rvalid_reg <= ace_rvalid;
            ace_rlast_reg  <= ace_rlast;
            ace_rresp_reg  <= ace_rresp;
        end
    end

    assign line_wdata = ace_rvalid ? ace_rdata : ace_rdata_reg;

    //===========================================
    // Response Path
    //===========================================
    assign core_rdata   = data_rdata;
    assign core_rresp   = hit ? 2'b00 : 2'b01;
    assign core_rvalid  = state_read;
    assign core_rlast   = 1'b1;
    assign core_bresp   = 2'b00;
    assign core_bvalid  = state_write;
    assign l2_ready     = 1'b1;
    assign l2_parity_err= 1'b0;

    //===========================================
    // Performance Counters
    //===========================================
    reg [31:0] hit_count_reg;
    reg [31:0] miss_count_reg;
    reg [31:0] evict_count_reg;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            hit_count_reg    <= 32'h0;
            miss_count_reg   <= 32'h0;
            evict_count_reg  <= 32'h0;
        end else begin
            if (state_idle & (core_read | core_write)) begin
                if (hit) begin
                    hit_count_reg <= hit_count_reg + 1;
                end else begin
                    miss_count_reg <= miss_count_reg + 1;
                end
            end
            if (state_evict & ace_bvalid) begin
                evict_count_reg <= evict_count_reg + 1;
            end
        end
    end

    assign perf_hit_count   = hit_count_reg;
    assign perf_miss_count  = miss_count_reg;
    assign perf_evict_count = evict_count_reg;

endmodule

//===========================================
// L2 Tag RAM
//===========================================
module l2_tag_ram #(
    parameter WIDTH = 40,
    parameter DEPTH = 256,
    parameter NUM_WAYS = 8
) (
    input  wire            clk,
    input  wire            rst_n,

    input  wire [$clog2(DEPTH)-1:0] index,
    input  wire [NUM_WAYS-1:0]      way_read,
    output wire [NUM_WAYS*WIDTH-1:0]tag_read,
    output wire [NUM_WAYS-1:0]      valid_read,
    output wire [NUM_WAYS-1:0]      dirty_read,

    input  wire [NUM_WAYS-1:0]      way_write,
    input  wire [WIDTH-1:0]         tag_write,
    input  wire                     valid_write,
    input  wire                     dirty_write,

    input  wire                     l2_flush,
    input  wire                     l2_inv
);

    localparam ADDR_WIDTH = $clog2(DEPTH);

    reg [WIDTH-1:0]                 tag_mem [0:DEPTH-1][0:NUM_WAYS-1];
    reg                             valid_mem [0:DEPTH-1][0:NUM_WAYS-1];
    reg                             dirty_mem [0:DEPTH-1][0:NUM_WAYS-1];

    integer i, j;

    always @(posedge clk) begin
        for (i = 0; i < NUM_WAYS; i = i + 1) begin
            if (way_write[i]) begin
                tag_mem[index][i]    <= tag_write;
                valid_mem[index][i]  <= valid_write;
                dirty_mem[index][i]  <= dirty_write;
            end
            if (l2_flush) begin
                valid_mem[index][i]  <= 1'b0;
            end
        end
    end

    genvar w;
    generate
        for (w = 0; w < NUM_WAYS; w = w + 1) begin : TAG_OUT
            assign tag_read[w*WIDTH +: WIDTH]   = tag_mem[index][w];
            assign valid_read[w]                = valid_mem[index][w];
            assign dirty_read[w]                = dirty_mem[index][w];
        end
    endgenerate

endmodule

//===========================================
// L2 Data RAM
//===========================================
module l2_data_ram #(
    parameter WIDTH = 512,
    parameter DEPTH = 256,
    parameter NUM_WAYS = 8
) (
    input  wire            clk,
    input  wire            rst_n,

    input  wire [$clog2(DEPTH)-1:0] index,
    input  wire [NUM_WAYS-1:0]      way_read,
    output wire [WIDTH-1:0]         data_read,

    input  wire [NUM_WAYS-1:0]      way_write,
    input  wire [WIDTH-1:0]         data_write,
    input  wire [WIDTH/8-1:0]       byte_enable
);

    localparam ADDR_WIDTH = $clog2(DEPTH);
    localparam BYTE_WIDTH = 8;

    reg [BYTE_WIDTH-1:0]            data_mem [0:DEPTH-1][0:NUM_WAYS-1][WIDTH/BYTE_WIDTH-1:0];

    integer i, j, k;

    always @(posedge clk) begin
        for (i = 0; i < NUM_WAYS; i = i + 1) begin
            if (way_write[i]) begin
                for (k = 0; k < WIDTH/BYTE_WIDTH; k = k + 1) begin
                    if (byte_enable[k]) begin
                        data_mem[index][i][k] <= data_write[k*BYTE_WIDTH +: BYTE_WIDTH];
                    end
                end
            end
        end
    end

    wire [WIDTH-1:0] way_data [0:NUM_WAYS-1];
    genvar w, b;
    generate
        for (w = 0; w < NUM_WAYS; w = w + 1) begin : DATA_OUT
            for (b = 0; b < WIDTH/BYTE_WIDTH; b = b + 1) begin : BYTE_GEN
                assign way_data[w][b*BYTE_WIDTH +: BYTE_WIDTH] = data_mem[index][w][b];
            end
        end
    endgenerate

    assign data_read = way_data[0];

endmodule

//===========================================
// L2 LRU Replacement
//===========================================
module l2_lru #(
    parameter NUM_WAYS = 8,
    parameter NUM_SETS = 256
) (
    input  wire            clk,
    input  wire            rst_n,

    input  wire [$clog2(NUM_SETS)-1:0] index,
    input  wire [NUM_WAYS-1:0]         hit_way,
    input  wire [NUM_WAYS-1:0]         access_way,
    input  wire                        lru_update,
    output wire [NUM_WAYS-1:0]         lru_read
);

    reg [NUM_WAYS-1:0] lru_mem [0:NUM_SETS-1];

    integer i, w;

    always @(posedge clk) begin
        if (lru_update) begin
            for (w = 0; w < NUM_WAYS; w = w + 1) begin
                if (access_way[w]) begin
                    lru_mem[index][w] <= 1'b1;
                end else begin
                    lru_mem[index][w] <= 1'b0;
                end
            end
        end
    end

    assign lru_read = lru_mem[index];

endmodule

endmodule
