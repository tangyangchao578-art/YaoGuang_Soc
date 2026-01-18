// ============================================================================
// Module: l3_cache_top
// Description: L3 Cache顶层模块
// Version: 1.0
// Date: 2026-01-18
// ============================================================================

`timescale 1ns / 1ps

module l3_cache_top #(
    parameter CACHE_SIZE    = 8 * 1024 * 1024,  // 8 MB
    parameter WAYS          = 16,                // 16-way
    parameter LINE_SIZE     = 64,                // 64B line
    parameter NUM_MASTERS   = 16,                // 16 masters
    parameter DATA_WIDTH    = 512,               // 512-bit
    parameter TAG_WIDTH     = 22,                // 32 - 6 - 4 = 22
    parameter INDEX_WIDTH   = 12,                // 8MB / 64B / 16 = 8192 sets
    parameter OFFSET_WIDTH  = 6,                 // 64B = 6 bits
    parameter NUM_MSHR      = 32,
    parameter NUM_WB        = 8,
    parameter NUM_RB        = 8,
    parameter FREQ_TARGET   = 1500               // MHz
) (
    // 时钟和复位
    input  logic                         clk,
    input  logic                         rst_n,

    // 从接口（连接Master）
    input  logic [NUM_MASTERS-1:0]       saxi_awvalid,
    output logic [NUM_MASTERS-1:0]       saxi_awready,
    input  logic [NUM_MASTERS-1:0][31:0] saxi_awaddr,
    input  logic [NUM_MASTERS-1:0][7:0]  saxi_awlen,
    input  logic [NUM_MASTERS-1:0][2:0]  saxi_awsize,
    input  logic [NUM_MASTERS-1:0][1:0]  saxi_awburst,
    input  logic [NUM_MASTERS-1:0][3:0]  saxi_awqos,

    input  logic [NUM_MASTERS-1:0]       saxi_wvalid,
    output logic [NUM_MASTERS-1:0]       saxi_wready,
    input  logic [NUM_MASTERS-1:0][DATA_WIDTH-1:0] saxi_wdata,
    input  logic [NUM_MASTERS-1:0][63:0] saxi_wstrb,
    input  logic [NUM_MASTERS-1:0]       saxi_wlast,

    output logic [NUM_MASTERS-1:0]       saxi_bvalid,
    input  logic [NUM_MASTERS-1:0]       saxi_bready,
    output logic [NUM_MASTERS-1:0][1:0]  saxi_bresp,

    input  logic [NUM_MASTERS-1:0]       saxi_arvalid,
    output logic [NUM_MASTERS-1:0]       saxi_arready,
    input  logic [NUM_MASTERS-1:0][31:0] saxi_araddr,
    input  logic [NUM_MASTERS-1:0][7:0]  saxi_arlen,
    input  logic [NUM_MASTERS-1:0][2:0]  saxi_arsize,
    input  logic [NUM_MASTERS-1:0][1:0]  saxi_arburst,
    input  logic [NUM_MASTERS-1:0][3:0]  saxi_arqos,

    output logic [NUM_MASTERS-1:0]       saxi_rvalid,
    input  logic [NUM_MASTERS-1:0]       saxi_rready,
    output logic [NUM_MASTERS-1:0][DATA_WIDTH-1:0] saxi_rdata,
    output logic [NUM_MASTERS-1:0][1:0]  saxi_rresp,
    output logic [NUM_MASTERS-1:0]       saxi_rlast,

    // 主接口（连接NoC/DDR）
    output logic                         maxi_awvalid,
    input  logic                         maxi_awready,
    output logic [31:0]                  maxi_awaddr,
    output logic [7:0]                   maxi_awlen,
    output logic [2:0]                   maxi_awsize,
    output logic [1:0]                   maxi_awburst,
    output logic [3:0]                   maxi_awqos,

    output logic                         maxi_wvalid,
    input  logic                         maxi_wready,
    output logic [DATA_WIDTH-1:0]        maxi_wdata,
    output logic [63:0]                  maxi_wstrb,
    output logic                         maxi_wlast,

    input  logic                         maxi_bvalid,
    output logic                         maxi_bready,
    input  logic [1:0]                   maxi_bresp,

    output logic                         maxi_arvalid,
    input  logic                         maxi_arready,
    output logic [31:0]                  maxi_araddr,
    output logic [7:0]                   maxi_arlen,
    output logic [2:0]                   maxi_arsize,
    output logic [1:0]                   maxi_arburst,
    output logic [3:0]                   maxi_arqos,

    input  logic                         maxi_rvalid,
    output logic                         maxi_rready,
    input  logic [DATA_WIDTH-1:0]        maxi_rdata,
    input  logic [1:0]                   maxi_rresp,
    input  logic                         maxi_rlast,

    // 配置和控制
    input  logic [31:0]                  cfg_base_addr,
    input  logic                         cache_bypass,
    input  logic                         cache_flush,
    input  logic                         cache_invalidate,
    output logic [7:0]                   cache_status,
    output logic                         flush_done,
    output logic [31:0]                  hit_count,
    output logic [31:0]                  miss_count,

    // 中断
    output logic                         ecc_error_irq,
    output logic                         snoop_irq
);

    // 内部信号
    logic [INDEX_WIDTH-1:0]             index;
    logic [TAG_WIDTH-1:0]               tag;
    logic [OFFSET_WIDTH-1:0]            offset;

    // Tag Array接口
    logic [NUM_MASTERS-1:0]             tag_read_req;
    logic [NUM_MASTERS-1:0][INDEX_WIDTH-1:0] tag_read_index;
    logic [TAG_WIDTH-1:0]               tag_write_addr;
    logic [INDEX_WIDTH-1:0]             tag_write_index;
    logic [TAG_WIDTH-1:0]               tag_write_data;
    logic                               tag_write_en;
    logic [WAYS-1:0]                    tag_write_way;
    logic [WAYS-1:0]                    tag_hit_way[NUM_MASTERS];
    logic                               tag_hit[NUM_MASTERS];
    logic [WAYS-1:0]                    tag_dirty;
    logic [WAYS-1:0]                    tag_valid;

    // Data Array接口
    logic [NUM_MASTERS-1:0]             data_read_req;
    logic [NUM_MASTERS-1:0][INDEX_WIDTH-1:0] data_read_index;
    logic [WAYS-1:0]                    data_read_way;
    logic                               data_write_en;
    logic [INDEX_WIDTH-1:0]             data_write_index;
    logic [WAYS-1:0]                    data_write_way;
    logic [DATA_WIDTH-1:0]              data_write_data;
    logic [63:0]                        data_write_mask;
    logic [DATA_WIDTH-1:0]              data_read_data[NUM_MASTERS];

    // MSHR接口
    logic                               mshr_alloc;
    logic                               mshr_free;
    logic [31:0]                        mshr_addr;
    logic [NUM_MSHR-1:0]                mshr_avail;
    logic                               mshr_hit;
    logic [9:0]                         mshr_hit_id;

    // 替换接口
    logic [INDEX_WIDTH-1:0]             replace_index;
    logic [WAYS-1:0]                    replace_way;
    logic                               replace_valid;
    logic                               replace_dirty;

    // 仲裁信号
    logic [NUM_MASTERS-1:0]             read_grant;
    logic [NUM_MASTERS-1:0]             write_grant;
    logic [NUM_MASTERS-1:0]             read_arb_valid;
    logic [NUM_MASTERS-1:0]             write_arb_valid;

    // 统计计数
    logic [31:0]                        hit_count_int;
    logic [31:0]                        miss_count_int;
    logic                               flush_counter_done;

    // 地址解码
    assign index = saxi_arvalid[0] ? saxi_araddr[0][INDEX_WIDTH+OFFSET_WIDTH-1:OFFSET_WIDTH] : 
                      saxi_awaddr[0][INDEX_WIDTH+OFFSET_WIDTH-1:OFFSET_WIDTH];
    assign tag   = saxi_arvalid[0] ? saxi_araddr[0][31:INDEX_WIDTH+OFFSET_WIDTH] : 
                      saxi_awaddr[0][31:INDEX_WIDTH+OFFSET_WIDTH];
    assign offset = saxi_arvalid[0] ? saxi_araddr[0][OFFSET_WIDTH-1:0] : 
                       saxi_awaddr[0][OFFSET_WIDTH-1:0];

    // Request Handler实例化
    l3_request_handler #(
        .NUM_MASTERS(NUM_MASTERS),
        .NUM_MSHR(NUM_MSHR),
        .INDEX_WIDTH(INDEX_WIDTH),
        .TAG_WIDTH(TAG_WIDTH),
        .DATA_WIDTH(DATA_WIDTH)
    ) u_request_handler (
        .clk(clk),
        .rst_n(rst_n),
        .saxi_awvalid(saxi_awvalid),
        .saxi_awready(saxi_awready),
        .saxi_awaddr(saxi_awaddr),
        .saxi_awlen(saxi_awlen),
        .saxi_awsize(saxi_awsize),
        .saxi_awburst(saxi_awburst),
        .saxi_awqos(saxi_awqos),
        .saxi_wvalid(saxi_wvalid),
        .saxi_wready(saxi_wready),
        .saxi_wdata(saxi_wdata),
        .saxi_wstrb(saxi_wstrb),
        .saxi_wlast(saxi_wlast),
        .saxi_bvalid(saxi_bvalid),
        .saxi_bready(saxi_bready),
        .saxi_bresp(saxi_bresp),
        .saxi_arvalid(saxi_arvalid),
        .saxi_arready(saxi_arready),
        .saxi_araddr(saxi_araddr),
        .saxi_arlen(saxi_arlen),
        .saxi_arsize(saxi_arsize),
        .saxi_arburst(saxi_arburst),
        .saxi_arqos(saxi_arqos),
        .saxi_rvalid(saxi_rvalid),
        .saxi_rready(saxi_rready),
        .saxi_rdata(saxi_rdata),
        .saxi_rresp(saxi_rresp),
        .saxi_rlast(saxi_rlast),
        .tag_hit(tag_hit),
        .tag_hit_way(tag_hit_way),
        .tag_dirty(tag_dirty),
        .data_read_data(data_read_data),
        .mshr_alloc(mshr_alloc),
        .mshr_free(mshr_free),
        .mshr_addr(mshr_addr),
        .mshr_avail(mshr_avail),
        .replace_valid(replace_valid),
        .replace_index(replace_index),
        .replace_way(replace_way),
        .replace_dirty(replace_dirty),
        .maxi_awvalid(maxi_awvalid),
        .maxi_awready(maxi_awready),
        .maxi_awaddr(maxi_awaddr),
        .maxi_awlen(maxi_awlen),
        .maxi_awsize(maxi_awsize),
        .maxi_awburst(maxi_awburst),
        .maxi_awqos(maxi_awqos),
        .maxi_wvalid(maxi_wvalid),
        .maxi_wready(maxi_wready),
        .maxi_wdata(maxi_wdata),
        .maxi_wstrb(maxi_wstrb),
        .maxi_wlast(maxi_wlast),
        .maxi_bvalid(maxi_bvalid),
        .maxi_bready(maxi_bready),
        .maxi_bresp(maxi_bresp),
        .maxi_arvalid(maxi_arvalid),
        .maxi_arready(maxi_arready),
        .maxi_araddr(maxi_araddr),
        .maxi_arlen(maxi_arlen),
        .maxi_arsize(maxi_arsize),
        .maxi_arburst(maxi_arburst),
        .maxi_arqos(maxi_arqos),
        .maxi_rvalid(maxi_rvalid),
        .maxi_rready(maxi_rready),
        .maxi_rdata(maxi_rdata),
        .maxi_rresp(maxi_rresp),
        .maxi_rlast(maxi_rlast),
        .hit_count(hit_count_int),
        .miss_count(miss_count_int)
    );

    // Tag Array实例化
    l3_tag_array #(
        .WAYS(WAYS),
        .INDEX_WIDTH(INDEX_WIDTH),
        .TAG_WIDTH(TAG_WIDTH)
    ) u_tag_array (
        .clk(clk),
        .rst_n(rst_n),
        .read_req(tag_read_req),
        .read_index(tag_read_index),
        .write_addr(tag_write_addr),
        .write_index(tag_write_index),
        .write_data(tag_write_data),
        .write_en(tag_write_en),
        .write_way(tag_write_way),
        .hit_way(tag_hit_way),
        .hit(tag_hit),
        .dirty(tag_dirty),
        .valid(tag_valid),
        .replace_valid(replace_valid),
        .replace_index(replace_index),
        .replace_way(replace_way),
        .replace_dirty(replace_dirty),
        .cache_flush(cache_flush),
        .flush_done(flush_done)
    );

    // Data Array实例化
    l3_data_array #(
        .WAYS(WAYS),
        .INDEX_WIDTH(INDEX_WIDTH),
        .DATA_WIDTH(DATA_WIDTH)
    ) u_data_array (
        .clk(clk),
        .rst_n(rst_n),
        .read_req(data_read_req),
        .read_index(data_read_index),
        .read_way(data_read_way),
        .write_en(data_write_en),
        .write_index(data_write_index),
        .write_way(data_write_way),
        .write_data(data_write_data),
        .write_mask(data_write_mask),
        .read_data(data_read_data)
    );

    // MSHR实例化
    l3_mshr #(
        .NUM_MSHR(NUM_MSHR),
        .INDEX_WIDTH(INDEX_WIDTH),
        .TAG_WIDTH(TAG_WIDTH)
    ) u_mshr (
        .clk(clk),
        .rst_n(rst_n),
        .alloc(mshr_alloc),
        .free(mshr_free),
        .addr(mshr_addr),
        .avail(mshr_avail),
        .hit(mshr_hit),
        .hit_id(mshr_hit_id)
    );

    // PLRU实例化
    l3_plru #(
        .WAYS(WAYS)
    ) u_plru (
        .clk(clk),
        .rst_n(rst_n),
        .index(replace_index),
        .hit_way(tag_hit_way),
        .hit_valid(tag_hit),
        .replace_way(replace_way)
    );

    // 统计输出
    assign hit_count = hit_count_int;
    assign miss_count = miss_count_int;
    assign cache_status = {flush_done, ecc_error_irq, snoop_irq, 5'b0};

endmodule
