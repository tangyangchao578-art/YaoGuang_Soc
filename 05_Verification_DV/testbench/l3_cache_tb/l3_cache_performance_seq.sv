//-----------------------------------------------------------------------------
// File: l3_cache_performance_seq.sv
// Description: L3 Cache performance test sequence
// Test Points: L3-007, L3-008, L3-010
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef L3_CACHE_PERFORMANCE_SEQ_SV
`define L3_CACHE_PERFORMANCE_SEQ_SV

class l3_cache_performance_seq extends uvm_sequence#(l3_cache_transaction);
    `uvm_object_utils(l3_cache_performance_seq)

    l3_cache_config cfg;
    int num_bandwidth_tests = 5000;
    int num_latency_tests = 2000;
    int num_stress_tests = 10000;
    int concurrent_transactions = 50;

    function new(string name = "l3_cache_performance_seq");
        super.new(name);
    endtask

    task body();
        l3_cache_transaction tr;

        `uvm_info("L3_CACHE_PERFORMANCE_SEQ", "Starting performance test", UVM_LOW)

        fork
            measure_bandwidth(tr);
            measure_latency(tr);
            stress_test(tr);
        join

        `uvm_info("L3_CACHE_PERFORMANCE_SEQ", "Completed performance test", UVM_LOW)
    endtask

    task measure_bandwidth(l3_cache_transaction tr);
        int start_time, end_time;
        real bandwidth;

        `uvm_info("L3_CACHE_PERFORMANCE_SEQ", "Measuring bandwidth", UVM_LOW)

        start_time = $time;
        for(int i = 0; i < num_bandwidth_tests; i++) begin
            tr = l3_cache_transaction::type_id::create("tr_bw");
            start_item(tr);
            randomize_performance(tr);
            finish_item(tr);
        end
        end_time = $time;

        bandwidth = (num_bandwidth_tests * 512) / ((end_time - start_time) * 1000000);
        `uvm_info("L3_CACHE_PERFORMANCE_SEQ", $sformatf("Bandwidth: %0f GB/s", bandwidth), UVM_LOW)
    endtask

    task measure_latency(l3_cache_transaction tr);
        int start_time, end_time;
        int total_latency = 0;
        real avg_latency;

        `uvm_info("L3_CACHE_PERFORMANCE_SEQ", "Measuring latency", UVM_LOW)

        for(int i = 0; i < num_latency_tests; i++) begin
            start_time = $time;
            tr = l3_cache_transaction::type_id::create("tr_lat");
            start_item(tr);
            randomize_performance(tr);
            finish_item(tr);
            end_time = $time;
            total_latency += (end_time - start_time);
        end

        avg_latency = total_latency / num_latency_tests;
        `uvm_info("L3_CACHE_PERFORMANCE_SEQ", $sformatf("Average latency: %0f cycles", avg_latency), UVM_LOW)
    endtask

    task stress_test(l3_cache_transaction tr);
        l3_cache_transaction transactions[concurrent_transactions];
        int completed = 0;

        `uvm_info("L3_CACHE_PERFORMANCE_SEQ", "Running stress test", UVM_LOW)

        fork
            begin
                for(int i = 0; i < concurrent_transactions; i++) begin
                    automatic int idx = i;
                    fork
                        begin
                            for(int j = 0; j < num_stress_tests/concurrent_transactions; j++) begin
                                tr = l3_cache_transaction::type_id::create($sformatf("tr_stress_%0d_%0d", idx, j));
                                start_item(tr);
                                randomize_performance(tr);
                                finish_item(tr);
                                completed++;
                            end
                        end
                    join_none
                end
            end
        join
    endtask

    virtual function void randomize_performance(l3_cache_transaction tr);
        bit op_sel;
        op_sel = $urandom_range(0, 1);
        if(op_sel) tr.op = L3_OP_READ;
        else tr.op = L3_OP_WRITE;

        tr.addr = $urandom_range(0, 64'h0000_0002_0000_0000) & ~'h3F;
        tr.data = $urandom();
        tr.size = 64;
        tr.id = $urandom_range(0, 15);
        tr.priority = $urandom_range(0, 255);
    endfunction
endclass

class l3_cache_performance_test extends uvm_test;
    `uvm_component_utils(l3_cache_performance_test)

    l3_cache_env env;
    l3_cache_config cfg;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = l3_cache_env::type_id::create("env", this);
        cfg = l3_cache_config::type_id::create("cfg", this);
    endfunction

    task run_phase(uvm_phase phase);
        l3_cache_performance_seq seq;

        phase.raise_objection(this);
        seq = l3_cache_performance_seq::type_id::create("seq");
        seq.start(env.agent.sequencer);
        phase.drop_objection(this);
    endtask
endclass

`endif
