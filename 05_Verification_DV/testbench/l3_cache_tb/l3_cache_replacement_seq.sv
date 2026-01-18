//-----------------------------------------------------------------------------
// File: l3_cache_replacement_seq.sv
// Description: L3 Cache replacement policy test sequence
// Test Points: L3-003, L3-004
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef L3_CACHE_REPLACEMENT_SEQ_SV
`define L3_CACHE_REPLACEMENT_SEQ_SV

class l3_cache_replacement_seq extends uvm_sequence#(l3_cache_transaction);
    `uvm_object_utils(l3_cache_replacement_seq)

    l3_cache_config cfg;
    int num_eviction_tests = 400;
    int num_writeback_tests = 300;

    function new(string name = "l3_cache_replacement_seq");
        super.new(name);
    endtask

    task body();
        l3_cache_transaction tr;

        `uvm_info("L3_CACHE_REPLACEMENT_SEQ", "Starting replacement policy test", UVM_LOW)

        fork
            test_lru_replacement(tr);
            test_writeback_policy(tr);
            test_eviction(tr);
        join

        `uvm_info("L3_CACHE_REPLACEMENT_SEQ", "Completed replacement policy test", UVM_LOW)
    endtask

    task test_lru_replacement(l3_cache_transaction tr);
        for(int i = 0; i < num_eviction_tests/2; i++) begin
            tr = l3_cache_transaction::type_id::create("tr_lru");
            start_item(tr);
            randomize_lru(tr);
            finish_item(tr);
        end
    endtask

    task test_writeback_policy(l3_cache_transaction tr);
        for(int i = 0; i < num_writeback_tests; i++) begin
            tr = l3_cache_transaction::type_id::create("tr_writeback");
            start_item(tr);
            randomize_writeback(tr);
            finish_item(tr);
        end
    endtask

    task test_eviction(l3_cache_transaction tr);
        for(int i = 0; i < num_eviction_tests/2; i++) begin
            tr = l3_cache_transaction::type_id::create("tr_evict");
            start_item(tr);
            randomize_eviction(tr);
            finish_item(tr);
        end
    endtask

    virtual function void randomize_lru(l3_cache_transaction tr);
        tr.op = L3_OP_READ;
        tr.addr = $urandom_range(0, 64'h0000_0002_0000_0000) & ~'h3F;
        tr.data = 0;
        tr.size = 64;
        tr.id = $urandom_range(0, 15);
        tr.priority = $urandom_range(0, 255);
    endfunction

    virtual function void randomize_writeback(l3_cache_transaction tr);
        tr.op = L3_OP_WRITE;
        tr.addr = $urandom_range(0, 64'h0000_0002_0000_0000) & ~'h3F;
        tr.data = $urandom();
        tr.size = 64;
        tr.id = $urandom_range(0, 15);
        tr.priority = $urandom_range(0, 255);
    endfunction

    virtual function void randomize_eviction(l3_cache_transaction tr);
        tr.op = L3_OP_EVICT;
        tr.addr = $urandom_range(0, 64'h0000_0002_0000_0000) & ~'h3F;
        tr.data = 0;
        tr.size = 0;
        tr.id = $urandom_range(0, 15);
        tr.priority = $urandom_range(0, 255);
    endfunction
endclass

class l3_cache_replacement_test extends uvm_test;
    `uvm_component_utils(l3_cache_replacement_test)

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
        l3_cache_replacement_seq seq;

        phase.raise_objection(this);
        seq = l3_cache_replacement_seq::type_id::create("seq");
        seq.start(env.agent.sequencer);
        phase.drop_objection(this);
    endtask
endclass

`endif
