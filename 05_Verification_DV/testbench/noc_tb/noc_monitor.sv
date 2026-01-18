`ifndef NOC_MONITOR_SV
`define NOC_MONITOR_SV

class noc_monitor extends uvm_monitor;
    `uvm_component_utils(noc_monitor)

    uvm_analysis_port#(noc_seq_item) ap;
    virtual noc_if   vif;
    noc_seq_item     trans;

    function new(string name = "noc_monitor", uvm_component parent = null);
        super.new(name, parent);
        ap = new("ap", this);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual noc_if)::get(this, "", "noc_if", vif)) begin
            `uvm_fatal(get_name(), "Cannot get noc_if from config DB")
        end
    endfunction

    task run_phase(uvm_phase phase);
        forever begin
            @(posedge vif.clk);
            if(vif.valid && vif.ready) begin
                trans = noc_seq_item::type_id::create("trans");
                trans.packet_type = vif.packet_type;
                trans.src_id      = vif.src_id;
                trans.dst_id      = vif.dst_id;
                trans.addr        = vif.addr;
                trans.qos_level   = vif.qos_level;
                trans.burst_size  = vif.burst_size;
                trans.length      = vif.length;
                trans.data        = vif.data;
                trans.status      = vif.status;
                ap.write(trans);
            end
        end
    endtask
endclass

`endif
