//-----------------------------------------------------------------------------
// File: cpu_scoreboard.sv
// Description: CPU Subsystem verification scoreboard
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef CPU_SCOREBOARD_SV
`define CPU_SCOREBOARD_SV

class cpu_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(cpu_scoreboard)

    uvm_tlm_analysis_fifo#(cpu_transaction) cpu_fifo;
    uvm_tlm_analysis_fifo#(cpu_transaction) ref_fifo;

    cpu_transaction cpu_q[$];
    cpu_transaction ref_q[$];

    int passed_tests = 0;
    int failed_tests = 0;
    int total_transactions = 0;
    int error_count = 0;

    bit [`MAX_ADDR_BITS-1:0] mem [`MAX_MEM_SIZE];

    function new(string name, uvm_component parent);
        super.new(name, parent);
        cpu_fifo = new("cpu_fifo", this);
        ref_fifo = new("ref_fifo", this);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        initialize_memory();
    endfunction

    function void initialize_memory();
        for(int i = 0; i < `MAX_MEM_SIZE; i++) begin
            mem[i] = $urandom();
        end
    endfunction

    virtual task run_phase(uvm_phase phase);
        super.run_phase(phase);
        fork
            process_cpu_transactions();
            process_ref_transactions();
            compare_transactions();
        join_none
    endtask

    virtual task process_cpu_transactions();
        cpu_transaction tr;
        forever begin
            cpu_fifo.get(tr);
            cpu_q.push_back(tr);
            total_transactions++;
        end
    endtask

    virtual task process_ref_transactions();
        cpu_transaction tr;
        forever begin
            ref_fifo.get(tr);
            ref_q.push_back(tr);
        end
    endtask

    virtual task compare_transactions();
        cpu_transaction cpu_tr, ref_tr;
        forever begin
            if(cpu_q.size() > 0 && ref_q.size() > 0) begin
                cpu_tr = cpu_q.pop_front();
                ref_tr = ref_q.pop_front();
                compare_transaction(cpu_tr, ref_tr);
            end
            #1;
        end
    endtask

    virtual function void compare_transaction(cpu_transaction cpu_tr, cpu_transaction ref_tr);
        if(cpu_tr.compare(ref_tr)) begin
            `uvm_info("CPU_SCOREBOARD", $sformatf("Transaction passed: ADDR=0x%0h", cpu_tr.addr), UVM_LOW)
            passed_tests++;
        end else begin
            `uvm_error("CPU_SCOREBOARD", $sformatf("Transaction failed: CPU=0x%0h REF=0x%0h", cpu_tr.data, ref_tr.data))
            failed_tests++;
            error_count++;
        end
    endfunction

    virtual function void report_phase(uvm_phase phase);
        `uvm_info("CPU_SCOREBOARD", $sformatf("=== Scoreboard Report ==="), UVM_LOW)
        `uvm_info("CPU_SCOREBOARD", $sformatf("Total transactions: %0d", total_transactions), UVM_LOW)
        `uvm_info("CPU_SCOREBOARD", $sformatf("Passed: %0d", passed_tests), UVM_LOW)
        `uvm_info("CPU_SCOREBOARD", $sformatf("Failed: %0d", failed_tests), UVM_LOW)
        `uvm_info("CPU_SCOREBOARD", $sformatf("Error rate: %0.2f%%", (real'(error_count)/real'(total_transactions))*100), UVM_LOW)
    endfunction
endclass

`endif
