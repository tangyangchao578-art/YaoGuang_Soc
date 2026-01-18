//-----------------------------------------------------------------------------
// File: l3_cache_scoreboard.sv
// Description: L3 Cache scoreboard
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef L3_CACHE_SCOREBOARD_SV
`define L3_CACHE_SCOREBOARD_SV

class l3_cache_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(l3_cache_scoreboard)

    uvm_tlm_analysis_fifo#(l3_cache_transaction) l3_fifo;
    uvm_tlm_analysis_fifo#(l3_cache_transaction) ref_fifo;

    l3_cache_transaction l3_q[$];
    l3_cache_transaction ref_q[$];

    int passed_tests = 0;
    int failed_tests = 0;
    int total_transactions = 0;
    int error_count = 0;
    int hit_count = 0;
    int miss_count = 0;

    bit [`MAX_ADDR_BITS-1:0] l3_mem [`MAX_MEM_SIZE];

    function new(string name, uvm_component parent);
        super.new(name, parent);
        l3_fifo = new("l3_fifo", this);
        ref_fifo = new("ref_fifo", this);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        initialize_memory();
    endfunction

    function void initialize_memory();
        for(int i = 0; i < `MAX_MEM_SIZE; i++) begin
            l3_mem[i] = $urandom();
        end
    endfunction

    virtual task run_phase(uvm_phase phase);
        super.run_phase(phase);
        fork
            process_l3_transactions();
            process_ref_transactions();
            compare_transactions();
        join_none
    endtask

    virtual task process_l3_transactions();
        l3_cache_transaction tr;
        forever begin
            l3_fifo.get(tr);
            l3_q.push_back(tr);
            total_transactions++;
            if(tr.response == L3_RESP_HIT) hit_count++;
            else miss_count++;
        end
    endtask

    virtual task process_ref_transactions();
        l3_cache_transaction tr;
        forever begin
            ref_fifo.get(tr);
            ref_q.push_back(tr);
        end
    endtask

    virtual task compare_transactions();
        l3_cache_transaction l3_tr, ref_tr;
        forever begin
            if(l3_q.size() > 0 && ref_q.size() > 0) begin
                l3_tr = l3_q.pop_front();
                ref_tr = ref_q.pop_front();
                compare_transaction(l3_tr, ref_tr);
            end
            #1;
        end
    endtask

    virtual function void compare_transaction(l3_cache_transaction l3_tr, l3_cache_transaction ref_tr);
        if(l3_tr.compare(ref_tr)) begin
            `uvm_info("L3_CACHE_SCOREBOARD", $sformatf("Transaction passed: ADDR=0x%0h", l3_tr.addr), UVM_LOW)
            passed_tests++;
        end else begin
            `uvm_error("L3_CACHE_SCOREBOARD", $sformatf("Transaction failed: L3=0x%0h REF=0x%0h", l3_tr.data, ref_tr.data))
            failed_tests++;
            error_count++;
        end
    endfunction

    virtual function void report_phase(uvm_phase phase);
        real hit_rate;
        hit_rate = (total_transactions > 0) ? (real'(hit_count) / real'(total_transactions)) * 100 : 0;

        `uvm_info("L3_CACHE_SCOREBOARD", $sformatf("=== L3 Cache Scoreboard Report ==="), UVM_LOW)
        `uvm_info("L3_CACHE_SCOREBOARD", $sformatf("Total transactions: %0d", total_transactions), UVM_LOW)
        `uvm_info("L3_CACHE_SCOREBOARD", $sformatf("Hit count: %0d", hit_count), UVM_LOW)
        `uvm_info("L3_CACHE_SCOREBOARD", $sformatf("Miss count: %0d", miss_count), UVM_LOW)
        `uvm_info("L3_CACHE_SCOREBOARD", $sformatf("Hit rate: %0.1f%%", hit_rate), UVM_LOW)
        `uvm_info("L3_CACHE_SCOREBOARD", $sformatf("Passed: %0d", passed_tests), UVM_LOW)
        `uvm_info("L3_CACHE_SCOREBOARD", $sformatf("Failed: %0d", failed_tests), UVM_LOW)
    endfunction
endclass

`define MAX_ADDR_BITS 64
`define MAX_MEM_SIZE 1024
`endif
