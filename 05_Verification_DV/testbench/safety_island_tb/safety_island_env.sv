//-----------------------------------------------------------------------------
// Safety Island UVM Environment
// YaoGuang SoC ASIL-D Safety Module Verification
//-----------------------------------------------------------------------------
`ifndef SAFETY_ISLAND_ENV_SV
`define SAFETY_ISLAND_ENV_SV

class safety_island_env extends uvm_env;
    `uvm_component_utils(safety_island_env)
    
    safety_island_agent          agent;
    safety_island_coverage       coverage;
    safety_island_scoreboard     scoreboard;
    safety_island_env_config     cfg;
    
    uvm_tlm_analysis_fifo#(safety_island_transaction) agent_fifo;
    
    function new(string name = "safety_island_env", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if(!uvm_config_db#(safety_island_env_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("BUILD", "Cannot get cfg from config_db")
        end
        
        agent = safety_island_agent::type_id::create("agent", this);
        uvm_config_db#(safety_island_agent_config)::set(this, "agent", "cfg", cfg.agent_cfg);
        
        if(cfg.enable_coverage) begin
            coverage = safety_island_coverage::type_id::create("coverage", this);
        end
        
        scoreboard = safety_island_scoreboard::type_id::create("scoreboard", this);
        agent_fifo = new("agent_fifo", this);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        agent.monitor.ap.connect(agent_fifo.analysis_export);
        
        if(cfg.enable_coverage) begin
            agent.monitor.ap.connect(coverage.analysis_export);
        end
        
        scoreboard.agent_export = agent_fifo;
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        `uvm_info("ENV", "Safety Island Environment Started", UVM_LOW)
        
        #1us;
        
        phase.drop_objection(this);
    endtask
    
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("ENV", "Safety Island Environment Report", UVM_LOW)
    endfunction
endclass

class safety_island_env_config extends uvm_object;
    `uvm_object_utils(safety_island_env_config)
    
    safety_island_agent_config  agent_cfg;
    bit                          enable_coverage = 1;
    bit                          enable_scoreboard = 1;
    int                          num_iterations = 1000;
    
    function new(string name = "safety_island_env_config");
        super.new(name);
        agent_cfg = safety_island_agent_config::type_id::create("agent_cfg");
    endfunction
endclass

`endif
