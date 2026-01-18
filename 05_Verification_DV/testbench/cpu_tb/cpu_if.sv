//-----------------------------------------------------------------------------
// File: cpu_if.sv
// Description: CPU Subsystem verification interface
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef CPU_IF_SV
`define CPU_IF_SV

interface cpu_if(input clk, input rst_n);
    import uvm_pkg::*;

    bit [63:0] addr;
    bit [63:0] data;
    bit [7:0] opcode;
    bit [3:0] size;
    bit valid;
    bit ready;
    bit [1:0] privilege;
    bit [2:0] cache_op;
    bit [1:0] cache_level;
    bit mmu_state;
    bit [7:0] irq_type;
    bit [7:0] irq_prio;
    bit irq_enabled;
    bit [7:0] stall_reason;
    bit branch_predicted;
    bit [31:0] instruction;
    bit [63:0] pc;

    clocking cb @(posedge clk);
        input addr, data, opcode, size, valid, privilege;
        input cache_op, cache_level, mmu_state;
        input irq_type, irq_prio, irq_enabled;
        output ready;
    endclocking

    modport tb(clocking cb, input clk, rst_n);
endinterface

`endif
