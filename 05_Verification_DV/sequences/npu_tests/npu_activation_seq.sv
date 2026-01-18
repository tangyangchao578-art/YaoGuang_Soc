`ifndef NPU_ACTIVATION_SEQ_SV
`define NPU_ACTIVATION_SEQ_SV

class npu_activation_seq extends uvm_sequence#(npu_cluster_seq_item);
    `uvm_object_utils(npu_activation_seq)

    rand int       num_transactions;
    rand bit[7:0]  op_type;
    rand bit[15:0] matrix_size;

    constraint trans_cons {
        num_transactions inside {[10:50]};
    }

    function new(string name = "npu_activation_seq");
        super.new(name);
        num_transactions = 20;
    endfunction

    task body();
        for(int i = 0; i < num_transactions; i++) begin
            npu_cluster_seq_item req;
            req = npu_cluster_seq_item::type_id::create("req");
            start_item(req);
            req.op_type      = npu_op_type_e'(op_type);
            req.data_width   = 16;
            req.matrix_size  = matrix_size;
            req.base_addr_a  = 32'h9000_0000 + i * 4096;
            req.base_addr_out = 32'h9001_0000 + i * 4096;
            finish_item(req);
        end
    endtask
endclass

class npu_relu_seq extends uvm_sequence#(npu_cluster_seq_item);
    `uvm_object_utils(npu_relu_seq)

    rand int       num_transactions;
    rand bit[15:0] matrix_size;
    bit[31:0]      base_addr;

    function new(string name = "npu_relu_seq");
        super.new(name);
        num_transactions = 25;
    endfunction

    task body();
        for(int i = 0; i < num_transactions; i++) begin
            npu_cluster_seq_item req;
            req = npu_cluster_seq_item::type_id::create("req");
            start_item(req);
            req.op_type      = OP_RELU;
            req.data_width   = 16;
            req.matrix_size  = matrix_size;
            req.base_addr_a  = base_addr + i * matrix_size * matrix_size * 2;
            req.base_addr_out = base_addr + i * matrix_size * matrix_size * 2 + 32768;
            finish_item(req);
        end
    endtask
endclass

class npu_sigmoid_seq extends uvm_sequence#(npu_cluster_seq_item);
    `uvm_object_utils(npu_sigmoid_seq)

    rand int       num_transactions;
    rand bit[15:0] matrix_size;
    bit[31:0]      base_addr;

    function new(string name = "npu_sigmoid_seq");
        super.new(name);
        num_transactions = 25;
    endfunction

    task body();
        for(int i = 0; i < num_transactions; i++) begin
            npu_cluster_seq_item req;
            req = npu_cluster_seq_item::type_id::create("req");
            start_item(req);
            req.op_type      = OP_SIGMOID;
            req.data_width   = 16;
            req.matrix_size  = matrix_size;
            req.base_addr_a  = base_addr + i * matrix_size * matrix_size * 2;
            req.base_addr_out = base_addr + i * matrix_size * matrix_size * 2 + 32768;
            finish_item(req);
        end
    endtask
endclass

class npu_tanh_seq extends uvm_sequence#(npu_cluster_seq_item);
    `uvm_object_utils(npu_tanh_seq)

    rand int       num_transactions;
    rand bit[15:0] matrix_size;
    bit[31:0]      base_addr;

    function new(string name = "npu_tanh_seq");
        super.new(name);
        num_transactions = 25;
    endfunction

    task body();
        for(int i = 0; i < num_transactions; i++) begin
            npu_cluster_seq_item req;
            req = npu_cluster_seq_item::type_id::create("req");
            start_item(req);
            req.op_type      = OP_TANH;
            req.data_width   = 16;
            req.matrix_size  = matrix_size;
            req.base_addr_a  = base_addr + i * matrix_size * matrix_size * 2;
            req.base_addr_out = base_addr + i * matrix_size * matrix_size * 2 + 32768;
            finish_item(req);
        end
    endtask
endclass

`endif
