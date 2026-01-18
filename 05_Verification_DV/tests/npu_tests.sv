`ifndef NPU_TESTS_SV
`define NPU_TESTS_SV

class npu_base_test extends uvm_test;
    `uvm_component_utils(npu_base_test)

    npu_cluster_env       env;
    npu_cluster_env_config cfg;

    function new(string name = "npu_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        cfg = new();
        cfg.is_active = 1;
        cfg.has_scoreboard = 1;
        cfg.has_coverage = 1;
        uvm_config_db#(npu_cluster_env_config)::set(this, "*", "npu_cluster_env_config", cfg);
        env = npu_cluster_env::type_id::create("env", this);
    endfunction

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        #1000;
        phase.drop_objection(this);
    endtask
endclass

class npu_sanity_test extends npu_base_test;
    `uvm_component_utils(npu_sanity_test)

    npu_matmul_seq matmul_seq;

    function new(string name = "npu_sanity_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        matmul_seq = npu_matmul_seq::type_id::create("matmul_seq");
        matmul_seq.start(env.agent.sequencer);
        #500;
        phase.drop_objection(this);
    endtask
endclass

class npu_matmul_test extends npu_base_test;
    `uvm_component_utils(npu_matmul_test)

    npu_matmul_int8_seq   int8_seq;
    npu_matmul_int16_seq  int16_seq;
    npu_matmul_fp16_seq   fp16_seq;

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        int8_seq = npu_matmul_int8_seq::type_id::create("int8_seq");
        int16_seq = npu_matmul_int16_seq::type_id::create("int16_seq");
        fp16_seq = npu_matmul_fp16_seq::type_id::create("fp16_seq");

        fork
            int8_seq.start(env.agent.sequencer);
            int16_seq.start(env.agent.sequencer);
            fp16_seq.start(env.agent.sequencer);
        join

        #1000;
        phase.drop_objection(this);
    endtask
endclass

class npu_activation_test extends npu_base_test;
    `uvm_component_utils(npu_activation_test)

    npu_relu_seq    relu_seq;
    npu_sigmoid_seq sigmoid_seq;
    npu_tanh_seq    tanh_seq;

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        relu_seq = npu_relu_seq::type_id::create("relu_seq");
        sigmoid_seq = npu_sigmoid_seq::type_id::create("sigmoid_seq");
        tanh_seq = npu_tanh_seq::type_id::create("tanh_seq");

        fork
            relu_seq.start(env.agent.sequencer);
            sigmoid_seq.start(env.agent.sequencer);
            tanh_seq.start(env.agent.sequencer);
        join

        #1000;
        phase.drop_objection(this);
    endtask
endclass

class npu_pooling_test extends npu_base_test;
    `uvm_component_utils(npu_pooling_test)

    npu_pool_max_seq max_seq;
    npu_pool_avg_seq avg_seq;

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        max_seq = npu_pool_max_seq::type_id::create("max_seq");
        avg_seq = npu_pool_avg_seq::type_id::create("avg_seq");

        fork
            max_seq.start(env.agent.sequencer);
            avg_seq.start(env.agent.sequencer);
        join

        #1000;
        phase.drop_objection(this);
    endtask
endclass

class npu_performance_test extends npu_base_test;
    `uvm_component_utils(npu_performance_test)

    npu_performance_seq perf_seq;
    npu_stress_seq      stress_seq;

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        perf_seq = npu_performance_seq::type_id::create("perf_seq");
        stress_seq = npu_stress_seq::type_id::create("stress_seq");

        fork
            perf_seq.start(env.agent.sequencer);
            stress_seq.start(env.agent.sequencer);
        join

        #2000;
        phase.drop_objection(this);
    endtask
endclass

`endif
