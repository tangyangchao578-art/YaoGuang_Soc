`ifndef NPU_CLUSTER_ENV_SV
`define NPU_CLUSTER_ENV_SV

class npu_cluster_env extends uvm_env;
    `uvm_component_utils(npu_cluster_env)

    npu_cluster_agent        agent;
    npu_cluster_scoreboard   scoreboard;
    npu_cluster_coverage     coverage;
    npu_cluster_env_config   cfg;

    uvm_table_printer        printer;

    function new(string name = "npu_cluster_env", uvm_component parent = null);
        super.new(name, parent);
        printer = new();
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        cfg = npu_cluster_env_config::type_id::create("cfg");
        if(!uvm_config_db#(npu_cluster_env_config)::get(this, "", "npu_cluster_env_config", cfg)) begin
            `uvm_fatal(get_name(), "Cannot get npu_cluster_env_config from config DB")
        end

        uvm_config_db#(npu_cluster_env_config)::set(this, "*agent*", "npu_cluster_env_config", cfg);

        agent      = npu_cluster_agent::type_id::create("agent", this);
        scoreboard = npu_cluster_scoreboard::type_id::create("scoreboard", this);
        coverage   = npu_cluster_coverage::type_id::create("coverage", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        agent.mon.item_collected_port.connect(scoreboard.item_collected_export);
        agent.mon.item_collected_port.connect(coverage.item_collected_export);
    endfunction

    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info(get_name(), $sformatf("Environment Report:\n%s", printer.sprint()), UVM_LOW)
    endfunction
endclass

`endif
