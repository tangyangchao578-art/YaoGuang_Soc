//-----------------------------------------------------------------------------
// Safety Island Interface
// YaoGuang SoC ASIL-D Safety Module Verification
//-----------------------------------------------------------------------------
`ifndef SAFETY_ISLAND_IF_SV
`define SAFETY_ISLAND_IF_SV

interface safety_island_if(input bit clk, input bit rst_n);
    logic[7:0]   opcode;
    logic[31:0]  data;
    logic[31:0]  addr;
    logic[7:0]   id;
    logic        valid;
    logic        ready;
    logic[1:0]   resp;
    logic[31:0]  status;
    logic        error;
    logic        lockstep_match;
    logic[5:0]   ecc_status;
    logic        wdg_timeout;
    
    clocking drv_cb @(posedge clk);
        default input #1step output #1ns;
        output opcode, data, addr, id, valid;
        input ready, resp;
    endclocking
    
    clocking mon_cb @(posedge clk);
        default input #1step;
        input opcode, data, addr, id, valid, ready, resp, status, error, lockstep_match, ecc_status, wdg_timeout;
    endclocking
endinterface

`endif
