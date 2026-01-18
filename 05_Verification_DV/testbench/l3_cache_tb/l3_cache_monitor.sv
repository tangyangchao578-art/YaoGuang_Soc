//-----------------------------------------------------------------------------
// File: l3_cache_monitor.sv
// Description: L3 Cache monitor
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef L3_CACHE_MONITOR_SV
`define L3_CACHE_MONITOR_SV

class l3_cache_monitor extends uvm_monitor;
    `uvm_component_utils(l3_cache_monitor)

    virtual l3_cache_if vif;
    l3_cache_config cfg;

    uvm_analysis_port#(l3_cache_transaction) ap;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual l3_cache_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("L3_CACHE_MONITOR", "Virtual interface not found")
        end
        cfg = l3_cache_config::type_id::create("cfg", this);
        ap = new("ap", this);
    endtask

    task run_phase(uvm_phase phase);
        l3_cache_transaction tr;
        forever begin
            @(posedge vif.clk);
            if(vif.valid && vif.ready) begin
                tr = new();
                tr.addr = vif.addr;
                tr.data = vif.data;
                tr.op = vif.op;
                tr.id = vif.id;
                tr.size = vif.size;
                tr.response = vif.response;
                tr.timestamp = $time;
                tr.valid = 1;
                ap.write(tr);
            end
        end
    endtask
endclass

`endif
