//-----------------------------------------------------------------------------
// File: ethernet_performance_seq.sv
// Description: Ethernet Controller Performance Test Sequence
// Author: YaoGuang SoC DV Team
// Created: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef ETHERNET_PERFORMANCE_SEQ_SV
`define ETHERNET_PERFORMANCE_SEQ_SV

class ethernet_performance_seq extends uvm_sequence #(ethernet_transaction);
    `uvm_object_utils(ethernet_performance_seq)
    
    int num_transactions = 10000;
    real throughput;
    time start_time, end_time;
    
    function new(string name = "ethernet_performance_seq");
        super.new(name);
    endtask
    
    virtual task body();
        ethernet_transaction tr;
        
        start_time = $time;
        
        repeat(num_transactions) begin
            tr = ethernet_transaction::type_id::create("tr");
            start_item(tr);
            if(!tr.randomize() with {
                tx_valid == 1;
            }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
        
        end_time = $time;
        throughput = (num_transactions * 64) / (end_time - start_time);
        
        `uvm_info("PERF", $sformatf("Ethernet Throughput: %0.2f Gbps", throughput / 1e9), UVM_LOW)
    endtask
endclass

class ethernet_line_rate_seq extends uvm_sequence #(ethernet_transaction);
    `uvm_object_utils(ethernet_line_rate_seq)
    
    int cycle_count = 100000;
    
    function new(string name = "ethernet_line_rate_seq");
        super.new(name);
    endtask
    
    virtual task body();
        for(int i = 0; i < cycle_count; i++) begin
            ethernet_transaction tr;
            tr = ethernet_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with {
                tx_valid == 1;
            }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

`endif
