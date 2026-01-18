//-----------------------------------------------------------------------------
// Safety Island Sequencer
// YaoGuang SoC ASIL-D Safety Module Verification
//-----------------------------------------------------------------------------
`ifndef SAFETY_ISLAND_SEQUENCER_SV
`define SAFETY_ISLAND_SEQUENCER_SV

class safety_island_sequencer extends uvm_sequencer#(safety_island_transaction);
    `uvm_component_utils(safety_island_sequencer)
    
    safety_island_sequencer_config  cfg;
    
    function new(string name = "safety_island_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(safety_island_sequencer_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("SEQ", "Cannot get cfg from config_db")
        end
    endfunction
endclass

`endif
