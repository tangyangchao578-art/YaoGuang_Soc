`ifndef NPU_CLUSTER_MONITOR_SV
`define NPU_CLUSTER_MONITOR_SV

class npu_cluster_monitor extends uvm_monitor;
    `uvm_component_utils(npu_cluster_monitor)

    uvm_analysis_port#(npu_cluster_seq_item) ap;
    virtual npu_cluster_if   vif;
    npu_cluster_seq_item     trans;

    function new(string name = "npu_cluster_monitor", uvm_component parent = null);
        super.new(name, parent);
        ap = new("ap", this);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual npu_cluster_if)::get(this, "", "npu_cluster_if", vif)) begin
            `uvm_fatal(get_name(), "Cannot get npu_cluster_if from config DB")
        end
    endfunction

    task run_phase(uvm_phase phase);
        forever begin
            @(posedge vif.clk);
            if(vif.start_cmd && !vif.busy) begin
                trans = npu_cluster_seq_item::type_id::create("trans");
                trans.op_type       = vif.op_type;
                trans.data_width    = vif.data_width;
                trans.matrix_size   = vif.matrix_size;
                trans.base_addr_a   = vif.base_addr_a;
                trans.base_addr_b   = vif.base_addr_b;
                trans.base_addr_out = vif.base_addr_out;
                trans.status        = vif.status;
                trans.result_data   = vif.result_data;
                ap.write(trans);
            end
        end
    endtask
endclass

`endif
