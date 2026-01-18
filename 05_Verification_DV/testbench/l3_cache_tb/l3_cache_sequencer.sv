//-----------------------------------------------------------------------------
// File: l3_cache_sequencer.sv
// Description: L3 Cache sequencer
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef L3_CACHE_SEQUENCER_SV
`define L3_CACHE_SEQUENCER_SV

class l3_cache_sequencer extends uvm_sequencer#(l3_cache_transaction);
    `uvm_component_utils(l3_cache_sequencer)

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
endclass

`endif
