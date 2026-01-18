//-----------------------------------------------------------------------------
// File: cpu_cache_seq.sv
// Description: CPU Cache test sequence
// Test Points: CPU-CACHE-001 ~ CPU-CACHE-005
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef CPU_CACHE_SEQ_SV
`define CPU_CACHE_SEQ_SV

class cpu_cache_seq extends uvm_sequence#(cpu_transaction);
    `uvm_object_utils(cpu_cache_seq)

    cpu_config cfg;
    int num_sequences = 500;

    function new(string name = "cpu_cache_seq");
        super.new(name);
    endfunction

    task body();
        cpu_transaction tr;

        `uvm_info("CPU_CACHE_SEQ", "Starting cache operations test", UVM_LOW)

        fork
            test_l1_cache_read(tr);
            test_l1_cache_write(tr);
            test_l2_cache_coherency(tr);
            test_cache_flush(tr);
            test_cache_invalidate(tr);
        join

        `uvm_info("CPU_CACHE_SEQ", "Completed cache operations test", UVM_LOW)
    endtask

    task test_l1_cache_read(cpu_transaction tr);
        for(int i = 0; i < num_sequences/5; i++) begin
            tr = cpu_transaction::type_id::create("tr_l1_read");
            start_item(tr);
            randomize_l1_read(tr);
            finish_item(tr);
        end
    endtask

    task test_l1_cache_write(cpu_transaction tr);
        for(int i = 0; i < num_sequences/5; i++) begin
            tr = cpu_transaction::type_id::create("tr_l1_write");
            start_item(tr);
            randomize_l1_write(tr);
            finish_item(tr);
        end
    endtask

    task test_l2_cache_coherency(cpu_transaction tr);
        for(int i = 0; i < num_sequences/5; i++) begin
            tr = cpu_transaction::type_id::create("tr_l2_coherency");
            start_item(tr);
            randomize_l2_coherency(tr);
            finish_item(tr);
        end
    endtask

    task test_cache_flush(cpu_transaction tr);
        for(int i = 0; i < num_sequences/5; i++) begin
            tr = cpu_transaction::type_id::create("tr_flush");
            start_item(tr);
            randomize_cache_flush(tr);
            finish_item(tr);
        end
    endtask

    task test_cache_invalidate(cpu_transaction tr);
        for(int i = 0; i < num_sequences/5; i++) begin
            tr = cpu_transaction::type_id::create("tr_invalidate");
            start_item(tr);
            randomize_cache_invalidate(tr);
            finish_item(tr);
        end
    endtask

    virtual function void randomize_l1_read(cpu_transaction tr);
        tr.opcode = OP_LOAD;
        tr.cache_op = CACHE_NONE;
        tr.cache_level = LEVEL_L1;
        tr.addr = $urandom_range(0, cfg.l1_cache_size * 1024);
        tr.data = 0;
        tr.size = $urandom_range(1, 8);
        tr.privilege = PRIV_KERNEL;
    endfunction

    virtual function void randomize_l1_write(cpu_transaction tr);
        tr.opcode = OP_STORE;
        tr.cache_op = CACHE_NONE;
        tr.cache_level = LEVEL_L1;
        tr.addr = $urandom_range(0, cfg.l1_cache_size * 1024);
        tr.data = $urandom();
        tr.size = $urandom_range(1, 8);
        tr.privilege = PRIV_KERNEL;
    endfunction

    virtual function void randomize_l2_coherency(cpu_transaction tr);
        tr.opcode = OP_LOAD;
        tr.cache_op = CACHE_NONE;
        tr.cache_level = LEVEL_L2;
        tr.addr = $urandom_range(cfg.l1_cache_size * 1024, cfg.l2_cache_size * 1024);
        tr.data = 0;
        tr.size = $urandom_range(1, 8);
        tr.privilege = PRIV_KERNEL;
    endfunction

    virtual function void randomize_cache_flush(cpu_transaction tr);
        tr.opcode = OP_SYSTEM;
        tr.cache_op = CACHE_FLUSH;
        tr.cache_level = LEVEL_L1;
        tr.addr = $urandom_range(0, cfg.l1_cache_size * 1024);
        tr.data = 0;
        tr.size = 0;
        tr.privilege = PRIV_KERNEL;
    endfunction

    virtual function void randomize_cache_invalidate(cpu_transaction tr);
        tr.opcode = OP_SYSTEM;
        tr.cache_op = CACHE_INVALIDATE;
        tr.cache_level = LEVEL_L1;
        tr.addr = $urandom_range(0, cfg.l1_cache_size * 1024);
        tr.data = 0;
        tr.size = 0;
        tr.privilege = PRIV_KERNEL;
    endfunction
endclass

class cpu_cache_test extends uvm_test;
    `uvm_component_utils(cpu_cache_test)

    cpu_env env;
    cpu_config cfg;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = cpu_env::type_id::create("env", this);
        cfg = cpu_config::type_id::create("cfg", this);
    endfunction

    task run_phase(uvm_phase phase);
        cpu_cache_seq seq;

        phase.raise_objection(this);
        seq = cpu_cache_seq::type_id::create("seq");
        seq.start(env.agents[0].sequencer);
        phase.drop_objection(this);
    endtask
endclass

`endif
