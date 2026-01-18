`ifndef NPU_CLUSTER_SEQ_ITEM_SV
`define NPU_CLUSTER_SEQ_ITEM_SV

typedef enum bit[7:0] {
    OP_MATMUL_INT8  = 8'h01,
    OP_MATMUL_INT16 = 8'h02,
    OP_MATMUL_FP16  = 8'h03,
    OP_RELU         = 8'h10,
    OP_SIGMOID      = 8'h11,
    OP_TANH         = 8'h12,
    OP_POOL_MAX     = 8'h20,
    OP_POOL_AVG     = 8'h21
} npu_op_type_e;

class npu_cluster_seq_item extends uvm_sequence_item;
    `uvm_object_utils(npu_cluster_seq_item)

    rand npu_op_type_e  op_type;
    rand bit[7:0]       data_width;
    rand bit[15:0]      matrix_size;
    rand bit[31:0]      base_addr_a;
    rand bit[31:0]      base_addr_b;
    rand bit[31:0]      base_addr_out;
    bit                 status;
    bit[31:0]           result_data;
    string              op_name;

    constraint valid_data_width {
        data_width inside {8, 16, 32};
    }

    constraint valid_matrix_size {
        matrix_size inside {16, 64, 256, 512};
    }

    constraint valid_addr {
        base_addr_a[1:0] == 0;
        base_addr_b[1:0] == 0;
        base_addr_out[1:0] == 0;
    }

    function new(string name = "npu_cluster_seq_item");
        super.new(name);
        op_name = op_type.name();
    endfunction

    function string convert2string();
        return $sformatf("op_type=%s data_width=%0d matrix_size=%0d addr_a=0x%08x addr_b=0x%08x addr_out=0x%08x status=%0d",
            op_name, data_width, matrix_size, base_addr_a, base_addr_b, base_addr_out, status);
    endfunction

    function void do_copy(uvm_object rhs);
        npu_cluster_seq_item rhs_;
        super.do_copy(rhs);
        $cast(rhs_, rhs);
        op_type      = rhs_.op_type;
        data_width   = rhs_.data_width;
        matrix_size  = rhs_.matrix_size;
        base_addr_a  = rhs_.base_addr_a;
        base_addr_b  = rhs_.base_addr_b;
        base_addr_out= rhs_.base_addr_out;
        status       = rhs_.status;
        result_data  = rhs_.result_data;
    endfunction

    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        npu_cluster_seq_item rhs_;
        do_compare = super.do_compare(rhs, comparer);
        $cast(rhs_, rhs);
        do_compare &= comparer.compare_field("op_type", op_type, rhs_.op_type, 8);
        do_compare &= comparer.compare_field("data_width", data_width, rhs_.data_width, 8);
        do_compare &= comparer.compare_field("matrix_size", matrix_size, rhs_.matrix_size, 16);
        do_compare &= comparer.compare_field("status", status, rhs_.status, 1);
    endfunction
endclass

`endif
