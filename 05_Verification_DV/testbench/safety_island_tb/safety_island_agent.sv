//-----------------------------------------------------------------------------
// Safety Island UVM Agent
// YaoGuang SoC ASIL-D Safety Module Verification
//-----------------------------------------------------------------------------
`ifndef SAFETY_ISLAND_AGENT_SV
`define SAFETY_ISLAND_AGENT_SV

class safety_island_agent extends uvm_agent;
    `uvm_component_utils(safety_island_agent)
    
    safety_island_driver          driver;
    safety_island_monitor         monitor;
    safety_island_sequencer       sequencer;
    safety_island_agent_config    cfg;
    
    uvm_analysis_port#(safety_island_transaction) ap;
    
    function new(string name = "safety_island_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if(!uvm_config_db#(safety_island_agent_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("BUILD", "Cannot get cfg from config_db")
        end
        
        driver = safety_island_driver::type_id::create("driver", this);
        monitor = safety_island_monitor::type_id::create("monitor", this);
        sequencer = safety_island_sequencer::type_id::create("sequencer", this);
        
        if(cfg.is_active == UVM_ACTIVE) begin
            uvm_config_db#(safety_island_sequencer_config)::set(this, "sequencer", "cfg", cfg.seq_cfg);
        end
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        ap = monitor.ap;
        
        if(cfg.is_active == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end
    endfunction
    
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
    endfunction
endclass

class safety_island_agent_config extends uvm_object;
    `uvm_object_utils(safety_island_agent_config)
    
    uvm_active_passive_enum    is_active = UVM_ACTIVE;
    virtual safety_island_if   vif;
    safety_island_sequencer_config  seq_cfg;
    
    function new(string name = "safety_island_agent_config");
        super.new(name);
        seq_cfg = safety_island_sequencer_config::type_id::create("seq_cfg");
    endfunction
endclass

class safety_island_sequencer_config extends uvm_object;
    `uvm_object_utils(safety_island_sequencer_config)
    
    int                         max_iterations = 1000;
    int                         timeout_cycles = 10000;
    
    function new(string name = "safety_island_sequencer_config");
        super.new(name);
    endfunction
endclass

`endif
