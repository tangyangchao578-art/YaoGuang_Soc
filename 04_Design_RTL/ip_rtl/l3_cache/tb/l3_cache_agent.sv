// ============================================================================
// Class: l3_cache_agent
// Description: L3 Cache UVM Agent
// Version: 1.0
// ============================================================================

`ifndef L3_CACHE_AGENT_SV
`define L3_CACHE_AGENT_SV

class l3_cache_agent extends uvm_agent;

    l3_cache_driver        driver;
    l3_cache_monitor       monitor;
    l3_cache_sequencer     sequencer;

    l3_cache_config        cfg;

    `uvm_component_utils(l3_cache_agent)

    function new(string name = "l3_cache_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        if (!uvm_config_db#(l3_cache_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("CFG", "Cannot get cfg from config_db")
        end

        if (cfg.is_active) begin
            driver = l3_cache_driver::type_id::create("driver", this);
            sequencer = l3_cache_sequencer::type_id::create("sequencer", this);
        end

        monitor = l3_cache_monitor::type_id::create("monitor", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        if (cfg.is_active) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end
    endfunction

endclass

`endif
