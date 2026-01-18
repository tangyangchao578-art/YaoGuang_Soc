`ifndef NPU_PERFORMANCE_SEQ_SV
`define NPU_PERFORMANCE_SEQ_SV

class npu_performance_seq extends uvm_sequence#(npu_cluster_seq_item);
    `uvm_object_utils(npu_performance_seq)

    int       num_transactions;
    int       throughput_accum;
    int       latency_accum;
    real      avg_throughput;
    real      avg_latency;
    int       test_count;

    function new(string name = "npu_performance_seq");
        super.new(name);
        num_transactions = 100;
    endfunction

    task body();
        npu_cluster_seq_item req;
        int start_time, end_time;

        `uvm_info(get_name(), "Starting performance test", UVM_LOW)
        test_count = 0;
        throughput_accum = 0;
        latency_accum = 0;

        for(int i = 0; i < num_transactions; i++) begin
            req = npu_cluster_seq_item::type_id::create("req");
            start_item(req);
            randomize(req) with {
                op_type inside {OP_MATMUL_INT8, OP_MATMUL_INT16, OP_MATMUL_FP16};
                matrix_size inside {16, 64, 256};
            };
            start_time = $time();
            finish_item(req);
            end_time = $time();
            
            latency_accum += (end_time - start_time);
            throughput_accum += req.matrix_size * req.matrix_size * 2;
            test_count++;
        end

        avg_latency = latency_accum / test_count;
        avg_throughput = throughput_accum / num_transactions;

        `uvm_info(get_name(), $sformatf("Performance Results:"), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Total Operations: %0d", test_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Average Latency: %0.2f cycles", avg_latency), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Throughput: %0.2f ops/cycle", avg_throughput), UVM_LOW)
    endtask
endclass

class npu_stress_seq extends uvm_sequence#(npu_cluster_seq_item);
    `uvm_object_utils(npu_stress_seq)

    int       num_transactions;
    int       max_concurrent;

    function new(string name = "npu_stress_seq");
        super.new(name);
        num_transactions = 500;
        max_concurrent = 10;
    endfunction

    task body();
        npu_cluster_seq_item req[$];
        int active_count;

        `uvm_info(get_name(), "Starting stress test", UVM_LOW)

        for(int i = 0; i < num_transactions; i++) begin
            while(active_count >= max_concurrent) begin
                @(posedge req[0].vif.clk);
                active_count--;
            end

            req = npu_cluster_seq_item::type_id::create("req");
            randomize(req) with {
                op_type inside {OP_MATMUL_INT8, OP_RELU, OP_POOL_MAX};
                matrix_size == 64;
            };
            start_item(req);
            finish_item(req);
            active_count++;
        end

        `uvm_info(get_name(), $sformatf("Stress test completed: %0d operations", num_transactions), UVM_LOW)
    endtask
endclass

`endif
