`ifndef NOC_PERFORMANCE_SEQ_SV
`define NOC_PERFORMANCE_SEQ_SV

class noc_performance_seq extends uvm_sequence#(noc_seq_item);
    `uvm_object_utils(noc_performance_seq)

    int       num_transactions;
    int       throughput_packets;
    int       latency_cycles;
    real      avg_latency;
    real      bandwidth_gbps;

    function new(string name = "noc_performance_seq");
        super.new(name);
        num_transactions = 1000;
    endtask

    task body();
        noc_seq_item req;
        int start_time, end_time;
        int latency_total = 0;
        throughput_packets = 0;

        `uvm_info(get_name(), "Starting NoC performance test", UVM_LOW)

        for(int i = 0; i < num_transactions; i++) begin
            req = noc_seq_item::type_id::create("req");
            start_item(req);
            randomize(req) with {
                packet_type inside {NOC_PACKET_READ, NOC_PACKET_WRITE};
                src_id != dst_id;
            };
            start_time = $time();
            finish_item(req);
            end_time = $time();
            latency_total += (end_time - start_time);
            throughput_packets++;
        end

        avg_latency = latency_total / throughput_packets;
        bandwidth_gbps = (throughput_packets * 64 * 8) / (avg_latency * 0.001) / 1e9;

        `uvm_info(get_name(), $sformatf("NoC Performance Results:"), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Packets: %0d", throughput_packets), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Avg Latency: %0.2f cycles", avg_latency), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Bandwidth: %0.2f Gbps", bandwidth_gbps), UVM_LOW)
    endtask
endclass

class noc_burst_seq extends uvm_sequence#(noc_seq_item);
    `uvm_object_utils(noc_burst_seq)

    int       num_bursts;
    int       burst_length;
    int       inter_burst_gap;

    function new(string name = "noc_burst_seq");
        super.new(name);
        num_bursts = 50;
        burst_length = 16;
        inter_burst_gap = 10;
    endtask

    task body();
        for(int b = 0; b < num_bursts; b++) begin
            for(int i = 0; i < burst_length; i++) begin
                noc_seq_item req;
                req = noc_seq_item::type_id::create("req");
                start_item(req);
                req.packet_type = NOC_PACKET_WRITE;
                req.src_id      = $urandom_range(0, 7);
                req.dst_id      = $urandom_range(0, 7);
                req.qos_level   = 2;
                req.burst_size  = 3;
                req.length      = 16;
                finish_item(req);
            end
            repeat(inter_burst_gap) @(posedge cfg.vif.clk);
        end
    endtask
endclass

class noc_stress_seq extends uvm_sequence#(noc_seq_item);
    `uvm_object_utils(noc_stress_seq)

    int       total_packets;
    int       concurrent_senders;
    int       active_senders;

    function new(string name = "noc_stress_seq");
        super.new(name);
        total_packets = 5000;
        concurrent_senders = 8;
    endtask

    task body();
        noc_seq_item req_q[$];
        active_senders = 0;

        fork
            begin
                for(int i = 0; i < total_packets; i++) begin
                    while(active_senders >= concurrent_senders) begin
                        @(posedge cfg.vif.clk);
                    end
                    req_q.push_back(req);
                    active_senders++;
                end
            end
            begin
                while(req_q.size() > 0 || active_senders < total_packets) begin
                    if(req_q.size() > 0) begin
                        noc_seq_item req;
                        req = req_q.pop_front();
                        start_item(req);
                        finish_item(req);
                        active_senders--;
                    end
                    @(posedge cfg.vif.clk);
                end
            end
        join
    endtask
endclass

`endif
