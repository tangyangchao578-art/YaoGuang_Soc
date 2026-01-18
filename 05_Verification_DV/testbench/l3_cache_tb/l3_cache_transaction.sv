//-----------------------------------------------------------------------------
// File: l3_cache_transaction.sv
// Description: L3 Cache transaction definition
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef L3_CACHE_TRANSACTION_SV
`define L3_CACHE_TRANSACTION_SV

typedef enum bit [2:0] {
    L3_OP_READ = 3'b000,
    L3_OP_WRITE = 3'b001,
    L3_OP_CLEAN = 3'b010,
    L3_OP_INVALIDATE = 3'b011,
    L3_OP_EVICT = 3'b100,
    L3_OP_SNOOP = 3'b101,
    L3_OP_QUERY = 3'b110
} l3_cache_op_t;

typedef enum bit [1:0] {
    L3_RESP_HIT = 2'b00,
    L3_RESP_MISS = 2'b01,
    L3_RESP_STALL = 2'b10
} l3_cache_resp_t;

typedef enum bit [2:0] {
    L3_REPLACEMENT_LRU = 3'b000,
    L3_REPLACEMENT_RANDOM = 3'b001,
    L3_REPLACEMENT_FIFO = 3'b010
} l3_replacement_policy_t;

typedef enum bit [1:0] {
    L3_WB_WRITE_BACK = 2'b00,
    L3_WB_WRITE_THROUGH = 2'b01
} l3_write_policy_t;

class l3_cache_transaction extends uvm_sequence_item;
    `uvm_object_utils(l3_cache_transaction)

    rand l3_cache_op_t op;
    rand bit [63:0] addr;
    rand bit [511:0] data;
    rand bit [5:0] size;
    rand bit [3:0] id;
    rand bit [7:0] priority;
    bit [1:0] response;
    bit valid;
    bit ready;
    bit [63:0] timestamp;

    bit [63:0] tag;
    bit [9:0] index;
    bit [5:0] offset;
    bit [15:0] way;
    bit dirty;
    bit valid_bit;

    constraint addr_align {
        addr % l3_line_size == 0;
    }

    constraint size_range {
        size inside {[1:64]};
    }

    function new(string name = "l3_cache_transaction");
        super.new(name);
    endfunction

    function void decode_address();
        tag = addr[63:12];
        index = addr[11:2];
        offset = addr[5:0];
    endfunction

    function string convert2string();
        string s;
        $sformat(s, "op=%s addr=0x%0h id=%0d", op.name(), addr, id);
        return s;
    endfunction
endclass

`endif
