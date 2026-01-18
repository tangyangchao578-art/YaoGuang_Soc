`ifndef NPU_CLUSTER_DRIVER_SV
`define NPU_CLUSTER_DRIVER_SV

class npu_cluster_driver extends uvm_driver#(npu_cluster_seq_item);
    `uvm_component_utils(npu_cluster_driver)

    virtual npu_cluster_if   vif;

    function new(string name = "npu_cluster_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual npu_cluster_if)::get(this, "", "npu_cluster_if", vif)) begin
            `uvm_fatal(get_name(), "Cannot get npu_cluster_if from config DB")
        end
    endfunction

    task run_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(req);
            drive_item(req);
            seq_item_port.item_done();
        end
    endtask

    virtual task drive_item(npu_cluster_seq_item req);
        vif.op_type     <= req.op_type;
        vif.data_width  <= req.data_width;
        vif.matrix_size <= req.matrix_size;
        vif.base_addr_a <= req.base_addr_a;
        vif.base_addr_b <= req.base_addr_b;
        vif.base_addr_out <= req.base_addr_out;
        vif.start_cmd   <= 1'b1;

        wait(vif.done == 1'b1);
        @(posedge vif.clk);
        vif.start_cmd   <= 1'b0;
        @(posedge vif.clk);
    endtask
endclass

`endif
