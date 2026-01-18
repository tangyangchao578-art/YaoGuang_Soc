// ============================================================================
// Interface: l3_cache_intf
// Description: L3 Cache验证接口
// Version: 1.0
// ============================================================================

`ifndef L3_CACHE_INTF_SV
`define L3_CACHE_INTF_SV

interface l3_cache_intf (
    input logic clk,
    input logic rst_n
);

    // 从接口（Master连接）
    logic [15:0]                  saxi_awvalid;
    logic [15:0]                  saxi_awready;
    logic [15:0][31:0]            saxi_awaddr;
    logic [15:0][7:0]             saxi_awlen;
    logic [15:0][2:0]             saxi_awsize;
    logic [15:0][1:0]             saxi_awburst;
    logic [15:0][3:0]             saxi_awqos;

    logic [15:0]                  saxi_wvalid;
    logic [15:0]                  saxi_wready;
    logic [15:0][511:0]           saxi_wdata;
    logic [15:0][63:0]            saxi_wstrb;
    logic [15:0]                  saxi_wlast;

    logic [15:0]                  saxi_bvalid;
    logic [15:0]                  saxi_bready;
    logic [15:0][1:0]             saxi_bresp;

    logic [15:0]                  saxi_arvalid;
    logic [15:0]                  saxi_arready;
    logic [15:0][31:0]            saxi_araddr;
    logic [15:0][7:0]             saxi_arlen;
    logic [15:0][2:0]             saxi_arsize;
    logic [15:0][1:0]             saxi_arburst;
    logic [15:0][3:0]             saxi_arqos;

    logic [15:0]                  saxi_rvalid;
    logic [15:0]                  saxi_rready;
    logic [15:0][511:0]           saxi_rdata;
    logic [15:0][1:0]             saxi_rresp;
    logic [15:0]                  saxi_rlast;

    // 主接口（NoC连接）
    logic                         maxi_awvalid;
    logic                         maxi_awready;
    logic [31:0]                  maxi_awaddr;
    logic [7:0]                   maxi_awlen;
    logic [2:0]                   maxi_awsize;
    logic [1:0]                   maxi_awburst;
    logic [3:0]                   maxi_awqos;

    logic                         maxi_wvalid;
    logic                         maxi_wready;
    logic [511:0]                 maxi_wdata;
    logic [63:0]                  maxi_wstrb;
    logic                         maxi_wlast;

    logic                         maxi_bvalid;
    logic                         maxi_bready;
    logic [1:0]                   maxi_bresp;

    logic                         maxi_arvalid;
    logic                         maxi_arready;
    logic [31:0]                  maxi_araddr;
    logic [7:0]                   maxi_arlen;
    logic [2:0]                   maxi_arsize;
    logic [1:0]                   maxi_arburst;
    logic [3:0]                   maxi_arqos;

    logic                         maxi_rvalid;
    logic                         maxi_rready;
    logic [511:0]                 maxi_rdata;
    logic [1:0]                   maxi_rresp;
    logic                         maxi_rlast;

    // 时钟使能
    logic                         clk_en;

endinterface

`endif
