`ifndef DV_SEQUENCER_SVH
`define DV_SEQUENCER_SVH

class dv_sequencer extends uvm_sequencer #(dv_sequence_item);
  `uvm_component_utils(dv_sequencer)

  function new(string name = "dv_sequencer", uvm_component parent = null);
    super.new(name, parent);
  endfunction
endclass

`endif
