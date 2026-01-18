`ifndef NOC_DRIVER_SV
`define NOC_DRIVER_SV

class noc_driver extends uvm_driver#(noc_seq_item);
    `uvm_component_utils(noc_driver)

    virtual noc_if   vif;

    function new(string name = "noc_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual noc_if)::get(this, "", "noc_if", vif)) begin
            `uvm_fatal(get_name(), "Cannot get noc_if from config DB")
        end
    endfunction

    task run_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(req);
            drive_item(req);
            seq_item_port.item_done();
        end
    endtask

    virtual task drive_item(noc_seq_item req);
        vif.packet_type <= req.packet_type;
        vif.src_id      <= req.src_id;
        vif.dst_id      <= req.dst_id;
        vif.addr        <= req.addr;
        vif.qos_level   <= req.qos_level;
        vif.burst_size  <= req.burst_size;
        vif.length      <= req.length;
        vif.data        <= req.data;
        vif.valid       <= 1'b1;

        wait(vif.ready == 1'b1);
        @(posedge vif.clk);
        vif.valid       <= 1'b0;
        @(posedge vif.clk);
    endtask
endclass

`endif
