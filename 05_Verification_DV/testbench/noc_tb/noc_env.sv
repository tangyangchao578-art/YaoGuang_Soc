`ifndef NOC_ENV_SV
`define NOC_ENV_SV

class noc_env extends uvm_env;
    `uvm_component_utils(noc_env)

    noc_agent        agent;
    noc_traffic_gen  traffic_gen;
    noc_scoreboard   scoreboard;
    noc_coverage     coverage;
    noc_env_config   cfg;

    function new(string name = "noc_env", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        cfg = noc_env_config::type_id::create("cfg");
        if(!uvm_config_db#(noc_env_config)::get(this, "", "noc_env_config", cfg)) begin
            `uvm_fatal(get_name(), "Cannot get noc_env_config from config DB")
        end

        uvm_config_db#(noc_env_config)::set(this, "*agent*", "noc_env_config", cfg);
        uvm_config_db#(noc_env_config)::set(this, "*traffic_gen*", "noc_env_config", cfg);

        agent       = noc_agent::type_id::create("agent", this);
        traffic_gen = noc_traffic_gen::type_id::create("traffic_gen", this);
        scoreboard  = noc_scoreboard::type_id::create("scoreboard", this);
        coverage    = noc_coverage::type_id::create("coverage", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        agent.mon.item_collected_port.connect(scoreboard.item_collected_export);
        agent.mon.item_collected_port.connect(coverage.item_collected_export);
        traffic_gen.req_port.connect(agent.sequencer.req_export);
    endfunction
endclass

`endif
