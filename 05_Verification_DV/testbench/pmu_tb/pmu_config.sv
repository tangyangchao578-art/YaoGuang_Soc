`ifndef PMU_CONFIG_SV
`define PMU_CONFIG_SV

class pmu_env_config extends uvm_object;
    `uvm_object_utils(pmu_env_config)

    bit                 is_active;
    bit                 has_scoreboard;
    bit                 has_coverage;
    virtual pmu_if      vif;

    function new(string name = "pmu_env_config");
        super.new(name);
        is_active = 1;
        has_scoreboard = 1;
        has_coverage = 1;
    endfunction
endclass

class pmu_agent_config extends uvm_object;
    `uvm_object_utils(pmu_agent_config)

    bit     is_active;
    int     num_transactions;

    function new(string name = "pmu_agent_config");
        super.new(name);
        is_active = 1;
        num_transactions = 100;
    endfunction
endclass

`endif
