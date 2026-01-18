`ifndef NPU_MATMUL_SEQ_SV
`define NPU_MATMUL_SEQ_SV

class npu_matmul_seq extends uvm_sequence#(npu_cluster_seq_item);
    `uvm_object_utils(npu_matmul_seq)

    rand int       num_transactions;
    rand bit[7:0]  data_width;
    rand bit[15:0] matrix_size;
    bit[31:0]      base_addr;

    constraint trans_cons {
        num_transactions inside {[10:100]};
    }

    constraint addr_cons {
        base_addr[31:20] == 12'h800;
    }

    function new(string name = "npu_matmul_seq");
        super.new(name);
        num_transactions = 50;
    endfunction

    task body();
        for(int i = 0; i < num_transactions; i++) begin
            npu_cluster_seq_item req;
            req = npu_cluster_seq_item::type_id::create("req");
            start_item(req);
            req.op_type = $random() % 3 ? 
                ($random() % 2 ? OP_MATMUL_INT8 : OP_MATMUL_INT16) : OP_MATMUL_FP16;
            req.data_width   = data_width;
            req.matrix_size  = matrix_size;
            req.base_addr_a  = base_addr + i * matrix_size * matrix_size * (data_width/8) * 2;
            req.base_addr_b  = base_addr + i * matrix_size * matrix_size * (data_width/8) * 2 + 
                               matrix_size * matrix_size * (data_width/8);
            req.base_addr_out = base_addr + i * matrix_size * matrix_size * (data_width/8) * 4;
            finish_item(req);
        end
    endtask
endclass

class npu_matmul_int8_seq extends uvm_sequence#(npu_cluster_seq_item);
    `uvm_object_utils(npu_matmul_int8_seq)

    rand int       num_transactions;
    rand bit[15:0] matrix_size;

    constraint trans_cons {
        num_transactions inside {[20:50]};
    }

    function new(string name = "npu_matmul_int8_seq");
        super.new(name);
        num_transactions = 30;
    endfunction

    task body();
        for(int i = 0; i < num_transactions; i++) begin
            npu_cluster_seq_item req;
            req = npu_cluster_seq_item::type_id::create("req");
            start_item(req);
            req.op_type      = OP_MATMUL_INT8;
            req.data_width   = 8;
            req.matrix_size  = matrix_size;
            req.base_addr_a  = 32'h8000_0000 + i * 4096;
            req.base_addr_b  = 32'h8001_0000 + i * 4096;
            req.base_addr_out = 32'h8002_0000 + i * 4096;
            finish_item(req);
        end
    endtask
endclass

class npu_matmul_int16_seq extends uvm_sequence#(npu_cluster_seq_item);
    `uvm_object_utils(npu_matmul_int16_seq)

    rand int       num_transactions;
    rand bit[15:0] matrix_size;

    constraint trans_cons {
        num_transactions inside {[20:50]};
    }

    function new(string name = "npu_matmul_int16_seq");
        super.new(name);
        num_transactions = 30;
    endfunction

    task body();
        for(int i = 0; i < num_transactions; i++) begin
            npu_cluster_seq_item req;
            req = npu_cluster_seq_item::type_id::create("req");
            start_item(req);
            req.op_type      = OP_MATMUL_INT16;
            req.data_width   = 16;
            req.matrix_size  = matrix_size;
            req.base_addr_a  = 32'h8010_0000 + i * 8192;
            req.base_addr_b  = 32'h8011_0000 + i * 8192;
            req.base_addr_out = 32'h8012_0000 + i * 8192;
            finish_item(req);
        end
    endtask
endclass

class npu_matmul_fp16_seq extends uvm_sequence#(npu_cluster_seq_item);
    `uvm_object_utils(npu_matmul_fp16_seq)

    rand int       num_transactions;
    rand bit[15:0] matrix_size;

    constraint trans_cons {
        num_transactions inside {[20:50]};
    }

    function new(string name = "npu_matmul_fp16_seq");
        super.new(name);
        num_transactions = 30;
    endfunction

    task body();
        for(int i = 0; i < num_transactions; i++) begin
            npu_cluster_seq_item req;
            req = npu_cluster_seq_item::type_id::create("req");
            start_item(req);
            req.op_type      = OP_MATMUL_FP16;
            req.data_width   = 16;
            req.matrix_size  = matrix_size;
            req.base_addr_a  = 32'h8020_0000 + i * 8192;
            req.base_addr_b  = 32'h8021_0000 + i * 8192;
            req.base_addr_out = 32'h8022_0000 + i * 8192;
            finish_item(req);
        end
    endtask
endclass

`endif
