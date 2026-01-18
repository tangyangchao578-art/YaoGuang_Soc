//-----------------------------------------------------------------------------
// File: cpu_performance_seq.sv
// Description: CPU performance test sequence
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef CPU_PERFORMANCE_SEQ_SV
`define CPU_PERFORMANCE_SEQ_SV

class cpu_performance_seq extends uvm_sequence#(cpu_transaction);
    `uvm_object_utils(cpu_performance_seq)

    cpu_config cfg;
    int transaction_count = 10000;
    int throughput_transactions = 5000;
    int latency_transactions = 2000;
    int concurrent_transactions = 100;

    function new(string name = "cpu_performance_seq");
        super.new(name);
    endtask

    task body();
        cpu_transaction tr;

        `uvm_info("CPU_PERFORMANCE_SEQ", "Starting performance test", UVM_LOW)

        fork
            measure_throughput(tr);
            measure_latency(tr);
            test_concurrency(tr);
        join

        `uvm_info("CPU_PERFORMANCE_SEQ", "Completed performance test", UVM_LOW)
    endtask

    task measure_throughput(cpu_transaction tr);
        int start_time, end_time;
        real throughput;

        `uvm_info("CPU_PERFORMANCE_SEQ", "Measuring throughput", UVM_LOW)

        start_time = $time;
        for(int i = 0; i < throughput_transactions; i++) begin
            tr = cpu_transaction::type_id::create("tr_throughput");
            start_item(tr);
            randomize_performance_tr(tr);
            finish_item(tr);
        end
        end_time = $time;

        throughput = throughput_transactions / ((end_time - start_time) / 1e6);
        `uvm_info("CPU_PERFORMANCE_SEQ", $sformatf("Throughput: %0f MT/s", throughput), UVM_LOW)
    endtask

    task measure_latency(cpu_transaction tr);
        int start_time, end_time;
        int total_latency = 0;
        real avg_latency;

        `uvm_info("CPU_PERFORMANCE_SEQ", "Measuring latency", UVM_LOW)

        for(int i = 0; i < latency_transactions; i++) begin
            start_time = $time;
            tr = cpu_transaction::type_id::create("tr_latency");
            start_item(tr);
            randomize_performance_tr(tr);
            finish_item(tr);
            end_time = $time;
            total_latency += (end_time - start_time);
        end

        avg_latency = total_latency / latency_transactions;
        `uvm_info("CPU_PERFORMANCE_SEQ", $sformatf("Average latency: %0f cycles", avg_latency), UVM_LOW)
    endtask

    task test_concurrency(cpu_transaction tr);
        cpu_transaction transactions[concurrent_transactions];
        int completed = 0;

        `uvm_info("CPU_PERFORMANCE_SEQ", "Testing concurrency", UVM_LOW)

        fork
            begin
                for(int i = 0; i < concurrent_transactions; i++) begin
                    automatic int idx = i;
                    fork
                        begin
                            tr = cpu_transaction::type_id::create($sformatf("tr_concurrent_%0d", idx));
                            start_item(tr);
                            randomize_performance_tr(tr);
                            finish_item(tr);
                            completed++;
                        end
                    join_none
                end
            end
        join
    endtask

    virtual function void randomize_performance_tr(cpu_transaction tr);
        tr.opcode = cpu_opcode_t'($urandom_range(0, 3));
        tr.addr = $urandom_range(0, `MAX_MEM_SIZE * 64);
        tr.data = $urandom();
        tr.size = $urandom_range(1, 8);
        tr.privilege = PRIV_KERNEL;
        tr.cache_op = CACHE_NONE;
        tr.cache_level = LEVEL_L1;
        tr.mmu_state = 1;
    endfunction
endclass

class cpu_performance_test extends uvm_test;
    `uvm_component_utils(cpu_performance_test)

    cpu_env env;
    cpu_config cfg;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = cpu_env::type_id::create("env", this);
        cfg = cpu_config::type_id::create("cfg", this);
    endfunction

    task run_phase(uvm_phase phase);
        cpu_performance_seq seq;

        phase.raise_objection(this);
        seq = cpu_performance_seq::type_id::create("seq");
        seq.start(env.agents[0].sequencer);
        phase.drop_objection(this);
    endtask
endclass

`endif
