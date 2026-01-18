// ============================================================================
// Class: l3_cache_sequencer
// Description: L3 Cache Sequencer
// Version: 1.0
// ============================================================================

`ifndef L3_CACHE_SEQUENCER_SV
`define L3_CACHE_SEQUENCER_SV

class l3_cache_sequencer extends uvm_sequencer#(l3_cache_seq_item);

    `uvm_component_utils(l3_cache_sequencer)

    function new(string name = "l3_cache_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass

`endif
