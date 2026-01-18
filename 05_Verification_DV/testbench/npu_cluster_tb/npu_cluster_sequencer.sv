`ifndef NPU_CLUSTER_SEQUENCER_SV
`define NPU_CLUSTER_SEQUENCER_SV

class npu_cluster_sequencer extends uvm_sequencer#(npu_cluster_seq_item);
    `uvm_component_utils(npu_cluster_sequencer)

    function new(string name = "npu_cluster_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
endclass

`endif
