`ifndef PMU_ENV_SV
`define PMU_ENV_SV

class pmu_env extends uvm_env;
    `uvm_component_utils(pmu_env)

    pmu_agent        agent;
    pmu_scoreboard   scoreboard;
    pmu_coverage     coverage;
    pmu_env_config   cfg;

    function new(string name = "pmu_env", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        cfg = pmu_env_config::type_id::create("cfg");
        if(!uvm_config_db#(pmu_env_config)::get(this, "", "pmu_env_config", cfg)) begin
            `uvm_fatal(get_name(), "Cannot get pmu_env_config from config DB")
        end

        uvm_config_db#(pmu_env_config)::set(this, "*agent*", "pmu_env_config", cfg);

        agent      = pmu_agent::type_id::create("agent", this);
        scoreboard = pmu_scoreboard::type_id::create("scoreboard", this);
        coverage   = pmu_coverage::type_id::create("coverage", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        agent.mon.item_collected_port.connect(scoreboard.item_collected_export);
        agent.mon.item_collected_port.connect(coverage.item_collected_export);
    endfunction
endclass

`endif
