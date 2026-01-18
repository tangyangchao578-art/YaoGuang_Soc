`ifndef NPU_POOLING_SEQ_SV
`define NPU_POOLING_SEQ_SV

class npu_pooling_seq extends uvm_sequence#(npu_cluster_seq_item);
    `uvm_object_utils(npu_pooling_seq)

    rand int       num_transactions;
    rand bit[7:0]  op_type;
    rand bit[15:0] matrix_size;
    rand bit[3:0]  pool_size;
    rand bit[3:0]  stride;

    constraint trans_cons {
        num_transactions inside {[10:50]};
        pool_size inside {2, 4, 8};
        stride inside {1, 2, 4};
    }

    function new(string name = "npu_pooling_seq");
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
            req.base_addr_a  = 32'hA000_0000 + i * 4096;
            req.base_addr_out = 32'hA001_0000 + i * 1024;
            finish_item(req);
        end
    endtask
endclass

class npu_pool_max_seq extends uvm_sequence#(npu_cluster_seq_item);
    `uvm_object_utils(npu_pool_max_seq)

    rand int       num_transactions;
    rand bit[15:0] matrix_size;
    rand bit[3:0]  pool_size;
    rand bit[3:0]  stride;
    bit[31:0]      base_addr;

    constraint pool_cons {
        pool_size inside {2, 4};
        stride inside {1, 2};
    }

    function new(string name = "npu_pool_max_seq");
        super.new(name);
        num_transactions = 30;
    endfunction

    task body();
        for(int i = 0; i < num_transactions; i++) begin
            npu_cluster_seq_item req;
            req = npu_cluster_seq_item::type_id::create("req");
            start_item(req);
            req.op_type      = OP_POOL_MAX;
            req.data_width   = 16;
            req.matrix_size  = matrix_size;
            req.base_addr_a  = base_addr + i * matrix_size * matrix_size * 2;
            req.base_addr_out = base_addr + i * matrix_size * matrix_size * 2 + 16384;
            finish_item(req);
        end
    endtask
endclass

class npu_pool_avg_seq extends uvm_sequence#(npu_cluster_seq_item);
    `uvm_object_utils(npu_pool_avg_seq)

    rand int       num_transactions;
    rand bit[15:0] matrix_size;
    rand bit[3:0]  pool_size;
    rand bit[3:0]  stride;
    bit[31:0]      base_addr;

    constraint pool_cons {
        pool_size inside {2, 4};
        stride inside {1, 2};
    }

    function new(string name = "npu_pool_avg_seq");
        super.new(name);
        num_transactions = 30;
    endfunction

    task body();
        for(int i = 0; i < num_transactions; i++) begin
            npu_cluster_seq_item req;
            req = npu_cluster_seq_item::type_id::create("req");
            start_item(req);
            req.op_type      = OP_POOL_AVG;
            req.data_width   = 16;
            req.matrix_size  = matrix_size;
            req.base_addr_a  = base_addr + i * matrix_size * matrix_size * 2;
            req.base_addr_out = base_addr + i * matrix_size * matrix_size * 2 + 16384;
            finish_item(req);
        end
    endtask
endclass

`endif
