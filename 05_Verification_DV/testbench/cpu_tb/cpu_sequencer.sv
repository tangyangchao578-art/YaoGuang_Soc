//-----------------------------------------------------------------------------
// File: cpu_sequencer.sv
// Description: CPU Subsystem sequencer
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef CPU_SEQUENCER_SV
`define CPU_SEQUENCER_SV

class cpu_sequencer extends uvm_sequencer#(cpu_transaction);
    `uvm_component_utils(cpu_sequencer)

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
endclass

`endif
