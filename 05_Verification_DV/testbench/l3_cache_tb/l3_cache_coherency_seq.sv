//-----------------------------------------------------------------------------
// File: l3_cache_coherency_seq.sv
// Description: L3 Cache coherency test sequence
// Test Points: L3-005, L3-006
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef L3_CACHE_COHERENCY_SEQ_SV
`define L3_CACHE_COHERENCY_SEQ_SV

class l3_cache_coherency_seq extends uvm_sequence#(l3_cache_transaction);
    `uvm_object_utils(l3_cache_coherency_seq)

    l3_cache_config cfg;
    int num_coherency_tests = 300;

    function new(string name = "l3_cache_coherency_seq");
        super.new(name);
    endtask

    task body();
        l3_cache_transaction tr;

        `uvm_info("L3_CACHE_COHERENCY_SEQ", "Starting coherency test", UVM_LOW)

        fork
            test_snoop_protocol(tr);
            test_shared_data(tr);
            test_modified_data(tr);
        join

        `uvm_info("L3_CACHE_COHERENCY_SEQ", "Completed coherency test", UVM_LOW)
    endtask

    task test_snoop_protocol(l3_cache_transaction tr);
        for(int i = 0; i < num_coherency_tests/3; i++) begin
            tr = l3_cache_transaction::type_id::create("tr_snoop");
            start_item(tr);
            randomize_snoop(tr);
            finish_item(tr);
            #50;
        end
    endtask

    task test_shared_data(l3_cache_transaction tr);
        for(int i = 0; i < num_coherency_tests/3; i++) begin
            tr = l3_cache_transaction::type_id::create("tr_shared");
            start_item(tr);
            randomize_shared(tr);
            finish_item(tr);
            #50;
        end
    endtask

    task test_modified_data(l3_cache_transaction tr);
        for(int i = 0; i < num_coherency_tests/3; i++) begin
            tr = l3_cache_transaction::type_id::create("tr_modified");
            start_item(tr);
            randomize_modified(tr);
            finish_item(tr);
            #50;
        end
    endtask

    virtual function void randomize_snoop(l3_cache_transaction tr);
        tr.op = L3_OP_SNOOP;
        tr.addr = $urandom_range(0, 64'h0000_0002_0000_0000) & ~'h3F;
        tr.data = 0;
        tr.size = 64;
        tr.id = $urandom_range(0, 15);
        tr.priority = $urandom_range(0, 255);
    endfunction

    virtual function void randomize_shared(l3_cache_transaction tr);
        tr.op = L3_OP_READ;
        tr.addr = $urandom_range(0, 64'h0000_0002_0000_0000) & ~'h3F;
        tr.data = 0;
        tr.size = 64;
        tr.id = $urandom_range(0, 15);
        tr.priority = $urandom_range(0, 127);
    endfunction

    virtual function void randomize_modified(l3_cache_transaction tr);
        tr.op = L3_OP_WRITE;
        tr.addr = $urandom_range(0, 64'h0000_0002_0000_0000) & ~'h3F;
        tr.data = $urandom();
        tr.size = 64;
        tr.id = $urandom_range(0, 15);
        tr.priority = $urandom_range(0, 63);
    endfunction
endclass

class l3_cache_coherency_test extends uvm_test;
    `uvm_component_utils(l3_cache_coherency_test)

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
        l3_cache_coherency_seq seq;

        phase.raise_objection(this);
        seq = l3_cache_coherency_seq::type_id::create("seq");
        seq.start(env.agent.sequencer);
        phase.drop_objection(this);
    endtask
endclass

`endif
