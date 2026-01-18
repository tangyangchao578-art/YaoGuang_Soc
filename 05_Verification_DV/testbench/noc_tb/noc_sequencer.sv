`ifndef NOC_SEQUENCER_SV
`define NOC_SEQUENCER_SV

class noc_sequencer extends uvm_sequencer#(noc_seq_item);
    `uvm_component_utils(noc_sequencer)

    function new(string name = "noc_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
endclass

`endif
