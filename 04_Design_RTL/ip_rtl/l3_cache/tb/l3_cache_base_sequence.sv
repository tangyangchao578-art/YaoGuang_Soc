// ============================================================================
// Class: l3_cache_base_sequence
// Description: L3 Cache Base Sequence
// Version: 1.0
// ============================================================================

`ifndef L3_CACHE_BASE_SEQUENCE_SV
`define L3_CACHE_BASE_SEQUENCE_SV

class l3_cache_base_sequence extends uvm_sequence#(l3_cache_seq_item);

    `uvm_object_utils(l3_cache_base_sequence)

    function new(string name = "l3_cache_base_sequence");
        super.new(name);
    endfunction

endclass

`endif
