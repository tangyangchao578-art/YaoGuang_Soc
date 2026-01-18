`ifndef PMU_AGENT_SV
`define PMU_AGENT_SV

class pmu_agent extends uvm_agent;
    `uvm_component_utils(pmu_agent)

    pmu_sequencer   sequencer;
    pmu_driver      driver;
    pmu_monitor     monitor;
    pmu_agent_config cfg;

    uvm_analysis_port#(pmu_seq_item) ap;

    function new(string name = "pmu_agent", uvm_component parent = null);
        super.new(name, parent);
        ap = new("ap", this);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        cfg = pmu_agent_config::type_id::create("cfg");
        if(!uvm_config_db#(pmu_agent_config)::get(this, "", "pmu_agent_config", cfg)) begin
            `uvm_fatal(get_name(), "Cannot get pmu_agent_config from config DB")
        end

        if(cfg.is_active) begin
            sequencer = pmu_sequencer::type_id::create("sequencer", this);
            driver    = pmu_driver::type_id::create("driver", this);
        end
        monitor = pmu_monitor::type_id::create("monitor", this);
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
