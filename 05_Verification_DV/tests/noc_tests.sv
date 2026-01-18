`ifndef NOC_TESTS_SV
`define NOC_TESTS_SV

class noc_base_test extends dv_base_test;
    `uvm_component_utils(noc_base_test)

    noc_env        env;
    noc_env_config cfg;

    function new(string name = "noc_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        cfg = new();
        cfg.is_active = 1;
        cfg.has_scoreboard = 1;
        cfg.has_coverage = 1;
        cfg.num_transactions = 1000;
        uvm_config_db#(noc_env_config)::set(this, "*", "noc_env_config", cfg);
        env = noc_env::type_id::create("env", this);
    endfunction

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        #1000;
        phase.drop_objection(this);
    endtask
endclass

class noc_sanity_test extends noc_base_test;
    `uvm_component_utils(noc_sanity_test)

    noc_routing_seq routing_seq;

    function new(string name = "noc_sanity_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        routing_seq = noc_routing_seq::type_id::create("routing_seq");
        routing_seq.num_transactions = 100;
        routing_seq.start(env.agent.sequencer);
        #500;
        phase.drop_objection(this);
    endtask
endclass

class noc_routing_test extends noc_base_test;
    `uvm_component_utils(noc_routing_test)

    noc_mesh_routing_seq mesh_seq;
    noc_all_to_all_seq   all_to_all_seq;

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        mesh_seq = noc_mesh_routing_seq::type_id::create("mesh_seq");
        all_to_all_seq = noc_all_to_all_seq::type_id::create("all_to_all_seq");

        fork
            mesh_seq.start(env.agent.sequencer);
            all_to_all_seq.start(env.agent.sequencer);
        join

        #1000;
        phase.drop_objection(this);
    endtask
endclass

class noc_qos_test extends noc_base_test;
    `uvm_component_utils(noc_qos_test)

    noc_qos_seq          qos_seq;
    noc_qos_priority_seq priority_seq;
    noc_qos_fairness_seq fairness_seq;

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        qos_seq = noc_qos_seq::type_id::create("qos_seq");
        priority_seq = noc_qos_priority_seq::type_id::create("priority_seq");
        fairness_seq = noc_qos_fairness_seq::type_id::create("fairness_seq");

        fork
            qos_seq.start(env.agent.sequencer);
            priority_seq.start(env.agent.sequencer);
            fairness_seq.start(env.agent.sequencer);
        join

        #2000;
        phase.drop_objection(this);
    endtask
endclass

class noc_performance_test extends noc_base_test;
    `uvm_component_utils(noc_performance_test)

    noc_performance_seq perf_seq;
    noc_burst_seq       burst_seq;
    noc_stress_seq      stress_seq;

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        perf_seq = noc_performance_seq::type_id::create("perf_seq");
        burst_seq = noc_burst_seq::type_id::create("burst_seq");
        stress_seq = noc_stress_seq::type_id::create("stress_seq");

        fork
            perf_seq.start(env.agent.sequencer);
            burst_seq.start(env.agent.sequencer);
            stress_seq.start(env.agent.sequencer);
        join

        #3000;
        phase.drop_objection(this);
    endtask
endclass

`endif
