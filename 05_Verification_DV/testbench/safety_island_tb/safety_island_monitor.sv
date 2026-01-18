//-----------------------------------------------------------------------------
// Safety Island Monitor
// YaoGuang SoC ASIL-D Safety Module Verification
//-----------------------------------------------------------------------------
`ifndef SAFETY_ISLAND_MONITOR_SV
`define SAFETY_ISLAND_MONITOR_SV

class safety_island_monitor extends uvm_monitor;
    `uvm_component_utils(safety_island_monitor)
    
    virtual safety_island_if   vif;
    uvm_analysis_port#(safety_island_transaction) ap;
    
    function new(string name = "safety_island_monitor", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual safety_island_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("MON", "Cannot get vif from config_db")
        end
        ap = new("ap", this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        super.run_phase(phase);
        
        forever begin
            @(posedge vif.clk);
            if(vif.mon_cb.valid && vif.mon_cb.ready) begin
                safety_island_transaction tr;
                tr = safety_island_transaction::type_id::create("tr");
                tr.opcode = vif.mon_cb.opcode;
                tr.data = vif.mon_cb.data;
                tr.addr = vif.mon_cb.addr;
                tr.id = vif.mon_cb.id;
                tr.resp = vif.mon_cb.resp;
                tr.timestamp = $time;
                ap.write(tr);
            end
        end
    endtask
endclass

`endif
