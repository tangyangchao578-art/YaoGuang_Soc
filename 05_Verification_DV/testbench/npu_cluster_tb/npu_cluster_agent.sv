`ifndef NPU_CLUSTER_AGENT_SV
`define NPU_CLUSTER_AGENT_SV

class npu_cluster_agent extends uvm_agent;
    `uvm_component_utils(npu_cluster_agent)

    npu_cluster_sequencer   sequencer;
    npu_cluster_driver      driver;
    npu_cluster_monitor     monitor;
    npu_cluster_agent_config cfg;

    uvm_analysis_port#(npu_cluster_seq_item) ap;

    function new(string name = "npu_cluster_agent", uvm_component parent = null);
        super.new(name, parent);
        ap = new("ap", this);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        cfg = npu_cluster_agent_config::type_id::create("cfg");
        if(!uvm_config_db#(npu_cluster_agent_config)::get(this, "", "npu_cluster_agent_config", cfg)) begin
            `uvm_fatal(get_name(), "Cannot get npu_cluster_agent_config from config DB")
        end

        if(cfg.is_active) begin
            sequencer = npu_cluster_sequencer::type_id::create("sequencer", this);
            driver    = npu_cluster_driver::type_id::create("driver", this);
        end
        monitor = npu_cluster_monitor::type_id::create("monitor", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        if(cfg.is_active) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end
        monitor.ap.connect(ap);
    endfunction
endclass

`endif
