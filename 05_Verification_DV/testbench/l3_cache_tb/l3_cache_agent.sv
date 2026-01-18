//-----------------------------------------------------------------------------
// File: l3_cache_agent.sv
// Description: L3 Cache verification agent
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef L3_CACHE_AGENT_SV
`define L3_CACHE_AGENT_SV

class l3_cache_agent extends uvm_agent;
    `uvm_component_utils(l3_cache_agent)

    l3_cache_config cfg;
    l3_cache_sequencer sequencer;
    l3_cache_driver driver;
    l3_cache_monitor monitor;
    virtual l3_cache_if vif;

    uvm_analysis_port#(l3_cache_transaction) ap;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        if(!uvm_config_db#(virtual l3_cache_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("L3_CACHE_AGENT", "Virtual interface not found")
        end

        cfg = l3_cache_config::type_id::create("cfg", this);
        uvm_config_db#(l3_cache_config)::set(this, "*", "l3_cache_config", cfg);

        sequencer = l3_cache_sequencer::type_id::create("sequencer", this);
        driver = l3_cache_driver::type_id::create("driver", this);
        monitor = l3_cache_monitor::type_id::create("monitor", this);

        ap = new("ap", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        driver.seq_item_port.connect(sequencer.seq_item_export);
        monitor.ap.connect(ap);
    endfunction

    task run_phase(uvm_phase phase);
        super.run_phase(phase);
        fork
            monitor.run();
            driver.run();
        join_none
    endtask
endclass

`endif
