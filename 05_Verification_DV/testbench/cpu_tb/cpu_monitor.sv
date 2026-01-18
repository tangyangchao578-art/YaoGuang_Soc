//-----------------------------------------------------------------------------
// File: cpu_monitor.sv
// Description: CPU Subsystem monitor
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef CPU_MONITOR_SV
`define CPU_MONITOR_SV

class cpu_monitor extends uvm_monitor;
    `uvm_component_utils(cpu_monitor)

    virtual cpu_if vif;
    cpu_config cfg;

    uvm_analysis_port#(cpu_transaction) ap;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual cpu_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("CPU_MONITOR", "Virtual interface not found")
        end
        cfg = cpu_config::type_id::create("cfg", this);
        ap = new("ap", this);
    endtask

    task run_phase(uvm_phase phase);
        cpu_transaction tr;
        forever begin
            @(posedge vif.clk);
            if(vif.valid && vif.ready) begin
                tr = new();
                tr.addr = vif.addr;
                tr.data = vif.data;
                tr.opcode = vif.opcode;
                tr.size = vif.size;
                tr.privilege = vif.privilege;
                tr.cache_op = vif.cache_op;
                tr.irq_type = vif.irq_type;
                tr.irq_prio = vif.irq_prio;
                tr.irq_enabled = vif.irq_enabled;
                tr.stall_reason = vif.stall_reason;
                tr.branch_predicted = vif.branch_predicted;
                tr.timestamp = $time;
                tr.valid = 1;
                ap.write(tr);
            end
        end
    endtask
endclass

`endif
