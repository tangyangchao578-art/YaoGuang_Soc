`ifndef NOC_TRAFFIC_GEN_SV
`define NOC_TRAFFIC_GEN_SV

class noc_traffic_gen extends uvm_component;
    `uvm_component_utils(noc_traffic_gen)

    uvm_seq_item_prod_port#(noc_seq_item) req_port;
    noc_env_config   cfg;

    int              total_packets;
    int              packet_count;
    real             avg_latency;
    real             throughput;

    function new(string name = "noc_traffic_gen", uvm_component parent = null);
        super.new(name, parent);
        req_port = new("req_port", this);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        cfg = noc_env_config::type_id::create("cfg");
        if(!uvm_config_db#(noc_env_config)::get(this, "", "noc_env_config", cfg)) begin
            `uvm_fatal(get_name(), "Cannot get noc_env_config from config DB")
        end
    endfunction

    task run_phase(uvm_phase phase);
        noc_seq_item req;
        int start_time, end_time;
        int latency_accum = 0;

        `uvm_info(get_name(), "Starting traffic generation", UVM_LOW)
        packet_count = 0;
        total_packets = cfg.num_transactions;
        throughput = 0;

        forever begin
            if(packet_count >= total_packets) break;
            req_port.try_next(req);
            if(req != null) begin
                start_time = $time();
                req_port.put(req);
                end_time = $time();
                latency_accum += (end_time - start_time);
                packet_count++;
            end
            @(posedge cfg.vif.clk);
        end

        avg_latency = latency_accum / packet_count;
        throughput = packet_count / (avg_latency * 0.001);

        `uvm_info(get_name(), $sformatf("Traffic Gen Report: Packets=%0d, AvgLatency=%0.2f, Throughput=%0.2f",
            packet_count, avg_latency, throughput), UVM_LOW)
    endtask
endclass

`endif
