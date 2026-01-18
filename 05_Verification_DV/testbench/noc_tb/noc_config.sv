`ifndef NOC_CONFIG_SV
`define NOC_CONFIG_SV

class noc_env_config extends uvm_object;
    `uvm_object_utils(noc_env_config)

    bit                 is_active;
    bit                 has_scoreboard;
    bit                 has_coverage;
    int                 num_transactions;
    virtual noc_if      vif;

    function new(string name = "noc_env_config");
        super.new(name);
        is_active = 1;
        has_scoreboard = 1;
        has_coverage = 1;
        num_transactions = 1000;
    endfunction
endclass

class noc_agent_config extends uvm_object;
    `uvm_object_utils(noc_agent_config)

    bit     is_active;
    int     num_transactions;

    function new(string name = "noc_agent_config");
        super.new(name);
        is_active = 1;
        num_transactions = 1000;
    endfunction
endclass

`endif
