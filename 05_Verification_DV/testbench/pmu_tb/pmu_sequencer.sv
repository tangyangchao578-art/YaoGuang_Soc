`ifndef PMU_SEQUENCER_SV
`define PMU_SEQUENCER_SV

class pmu_sequencer extends uvm_sequencer#(pmu_seq_item);
    `uvm_component_utils(pmu_sequencer)

    function new(string name = "pmu_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
endclass

`endif
