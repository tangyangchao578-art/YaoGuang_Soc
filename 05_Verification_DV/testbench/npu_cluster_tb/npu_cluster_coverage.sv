`ifndef NPU_CLUSTER_COVERAGE_SV
`define NPU_CLUSTER_COVERAGE_SV

class npu_cluster_coverage extends uvm_subscriber#(npu_cluster_seq_item);
    `uvm_component_utils(npu_cluster_coverage)

    npu_cluster_seq_item  trans;

    covergroup npu_cluster_cg;
        option.per_instance = 1;
        op_type: coverpoint trans.op_type {
            bins MATMUL_INT8  = {OP_MATMUL_INT8};
            bins MATMUL_INT16 = {OP_MATMUL_INT16};
            bins MATMUL_FP16  = {OP_MATMUL_FP16};
            bins RELU         = {OP_RELU};
            bins SIGMOID      = {OP_SIGMOID};
            bins TANH         = {OP_TANH};
            bins POOL_MAX     = {OP_POOL_MAX};
            bins POOL_AVG     = {OP_POOL_AVG};
        }
        data_width: coverpoint trans.data_width {
            bins W8  = {8};
            bins W16 = {16};
            bins W32 = {32};
        }
        matrix_size: coverpoint trans.matrix_size {
            bins SMALL  = {16};
            bins MEDIUM = {64};
            bins LARGE  = {256};
        }
        status: coverpoint trans.status {
            bins SUCCESS = {0};
            bins ERROR   = {1};
        }
        cross_op_data: cross op_type, data_width;
        cross_all: cross op_type, data_width, matrix_size;
    endgroup

    function new(string name = "npu_cluster_coverage", uvm_component parent = null);
        super.new(name, parent);
        npu_cluster_cg = new();
    endfunction

    virtual function void write(T t);
        trans = t;
        npu_cluster_cg.sample();
    endfunction

    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info(get_name(), $sformatf("Coverage Report:"), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Overall Coverage: %0.2f%%", npu_cluster_cg.get_inst_coverage()), UVM_LOW)
    endfunction
endclass

`endif
