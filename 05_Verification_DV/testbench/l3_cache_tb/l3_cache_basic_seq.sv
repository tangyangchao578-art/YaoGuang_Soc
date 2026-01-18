//-----------------------------------------------------------------------------
// File: l3_cache_basic_seq.sv
// Description: L3 Cache basic read/write test sequence
// Test Points: L3-001, L3-002
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef L3_CACHE_BASIC_SEQ_SV
`define L3_CACHE_BASIC_SEQ_SV

class l3_cache_basic_seq extends uvm_sequence#(l3_cache_transaction);
    `uvm_object_utils(l3_cache_basic_seq)

    l3_cache_config cfg;
    int num_reads = 1000;
    int num_writes = 500;

    function new(string name = "l3_cache_basic_seq");
        super.new(name);
    endtask

    task body();
        l3_cache_transaction tr;

        `uvm_info("L3_CACHE_BASIC_SEQ", "Starting basic read/write test", UVM_LOW)

        fork
            perform_reads(tr);
            perform_writes(tr);
        join

        `uvm_info("L3_CACHE_BASIC_SEQ", "Completed basic read/write test", UVM_LOW)
    endtask

    task perform_reads(l3_cache_transaction tr);
        for(int i = 0; i < num_reads; i++) begin
            tr = l3_cache_transaction::type_id::create("tr_read");
            start_item(tr);
            randomize_read(tr);
            finish_item(tr);
        end
    endtask

    task perform_writes(l3_cache_transaction tr);
        for(int i = 0; i < num_writes; i++) begin
            tr = l3_cache_transaction::type_id::create("tr_write");
            start_item(tr);
            randomize_write(tr);
            finish_item(tr);
        end
    endtask

    virtual function void randomize_read(l3_cache_transaction tr);
        tr.op = L3_OP_READ;
        tr.addr = $urandom_range(0, 64'h0000_0002_0000_0000) & ~'h3F;
        tr.data = 0;
        tr.size = 64;
        tr.id = $urandom_range(0, 15);
        tr.priority = $urandom_range(0, 255);
    endfunction

    virtual function void randomize_write(l3_cache_transaction tr);
        tr.op = L3_OP_WRITE;
        tr.addr = $urandom_range(0, 64'h0000_0002_0000_0000) & ~'h3F;
        tr.data = $urandom();
        tr.size = 64;
        tr.id = $urandom_range(0, 15);
        tr.priority = $urandom_range(0, 255);
    endfunction
endclass

class l3_cache_basic_test extends uvm_test;
    `uvm_component_utils(l3_cache_basic_test)

    l3_cache_env env;
    l3_cache_config cfg;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = l3_cache_env::type_id::create("env", this);
        cfg = l3_cache_config::type_id::create("cfg", this);
    endfunction

    task run_phase(uvm_phase phase);
        l3_cache_basic_seq seq;

        phase.raise_objection(this);
        seq = l3_cache_basic_seq::type_id::create("seq");
        seq.start(env.agent.sequencer);
        phase.drop_objection(this);
    endtask
endclass

`endif
