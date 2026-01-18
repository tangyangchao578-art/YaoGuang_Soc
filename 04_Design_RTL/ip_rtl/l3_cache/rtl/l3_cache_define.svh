// ============================================================================
// Module: l3_cache_define
// Description: L3 Cache Common Definitions
// Version: 1.0
// ============================================================================

// Cache配置参数
parameter L3_CACHE_SIZE     = 8 * 1024 * 1024;   // 8 MB
parameter L3_WAYS           = 16;                 // 16-way
parameter L3_LINE_SIZE      = 64;                 // 64B
parameter L3_SETS           = L3_CACHE_SIZE / (L3_LINE_SIZE * L3_WAYS);
parameter L3_TAG_WIDTH      = 32 - $clog2(L3_LINE_SIZE) - $clog2(L3_SETS);
parameter L3_INDEX_WIDTH    = $clog2(L3_SETS);
parameter L3_OFFSET_WIDTH   = $clog2(L3_LINE_SIZE);
parameter L3_NUM_MASTERS    = 16;
parameter L3_NUM_MSHR       = 32;
parameter L3_NUM_WB         = 8;
parameter L3_NUM_RB         = 8;
parameter L3_DATA_WIDTH     = 512;

// 响应码
parameter RESP_OKAY         = 2'b00;
parameter RESP_EXOKAY       = 2'b01;
parameter RESP_SLVERR       = 2'b10;
parameter RESP_DECERR       = 2'b11;

// 突发类型
parameter BURST_FIXED       = 2'b00;
parameter BURST_INCR        = 2'b01;
parameter BURST_WRAP        = 2'b10;

// 状态
typedef enum logic [1:0] {
    L3_IDLE,
    L3_BUSY,
    L3_ERROR
} l3_state_t;

// 调试信号
`ifdef L3_CACHE_DEBUG
`define L3_DEBUG(msg) $display("[L3CACHE_DEBUG] %t: %s", $time, msg);
`else
`define L3_DEBUG(msg)
`endif
