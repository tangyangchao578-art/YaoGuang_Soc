//-----------------------------------------------------------------------------
// File: l3_cache_if.sv
// Description: L3 Cache verification interface
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef L3_CACHE_IF_SV
`define L3_CACHE_IF_SV

interface l3_cache_if(input clk, input rst_n);
    import uvm_pkg::*;

    bit [63:0] addr;
    bit [511:0] data;
    bit [5:0] size;
    bit [2:0] op;
    bit [3:0] id;
    bit [7:0] priority;
    bit valid;
    bit ready;
    bit [1:0] response;
    bit [63:0] snoop_addr;
    bit snoop_valid;
    bit snoop_response;

    clocking cb @(posedge clk);
        input addr, data, size, op, id, priority, valid;
        output ready, response, snoop_addr, snoop_valid, snoop_response;
    endclocking

    modport tb(clocking cb, input clk, rst_n);
endinterface

`endif
