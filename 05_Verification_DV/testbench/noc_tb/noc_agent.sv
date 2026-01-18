`ifndef NOC_AGENT_SV
`define NOC_AGENT_SV

class noc_agent extends uvm_agent;
    `uvm_component_utils(noc_agent)

    noc_sequencer   sequencer;
    noc_driver      driver;
    noc_monitor     monitor;
    noc_agent_config cfg;

    uvm_analysis_port#(noc_seq_item) ap;

    function new(string name = "noc_agent", uvm_component parent = null);
        super.new(name, parent);
        ap = new("ap", this);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        cfg = noc_agent_config::type_id::create("cfg");
        if(!uvm_config_db#(noc_agent_config)::get(this, "", "noc_agent_config", cfg)) begin
            `uvm_fatal(get_name(), "Cannot get noc_agent_config from config DB")
        end

        if(cfg.is_active) begin
            sequencer = noc_sequencer::type_id::create("sequencer", this);
            driver    = noc_driver::type_id::create("driver", this);
        end
        monitor = noc_monitor::type_id::create("monitor", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        if(cfg.is_active) begin
            driver.seq_item_port.connect(sequencer.req_export);
        end
        monitor.ap.connect(ap);
    endfunction
endclass

`endif
