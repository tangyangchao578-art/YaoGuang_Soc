//-----------------------------------------------------------------------------
// File: cpu_agent.sv
// Description: CPU Subsystem verification agent
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef CPU_AGENT_SV
`define CPU_AGENT_SV

class cpu_agent extends uvm_agent;
    `uvm_component_utils(cpu_agent)

    cpu_config cfg;
    cpu_sequencer sequencer;
    cpu_driver driver;
    cpu_monitor monitor;
    virtual cpu_if vif;

    uvm_analysis_port#(cpu_transaction) ap;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        if(!uvm_config_db#(virtual cpu_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("CPU_AGENT", "Virtual interface not found")
        end

        cfg = cpu_config::type_id::create("cfg", this);
        uvm_config_db#(cpu_config)::set(this, "*", "cpu_config", cfg);

        sequencer = cpu_sequencer::type_id::create("sequencer", this);
        driver = cpu_driver::type_id::create("driver", this);
        monitor = cpu_monitor::type_id::create("monitor", this);

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
