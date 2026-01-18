// ============================================================================
// Class: l3_cache_virtual_sequencer
// Description: L3 Cache Virtual Sequencer
// Version: 1.0
// ============================================================================

`ifndef L3_CACHE_VIRTUAL_SEQUENCER_SV
`define L3_CACHE_VIRTUAL_SEQUENCER_SV

class l3_cache_virtual_sequencer extends uvm_sequencer;

    l3_cache_sequencer             agent_seqr;
    l3_cache_config                cfg;

    `uvm_component_utils(l3_cache_virtual_sequencer)

    function new(string name = "l3_cache_virtual_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass

`endif
