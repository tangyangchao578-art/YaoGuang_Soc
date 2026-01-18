//-----------------------------------------------------------------------------
// File: pcie_performance_seq.sv
// Description: PCIe Controller Performance Test Sequence
// Author: YaoGuang SoC DV Team
// Created: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef PCIE_PERFORMANCE_SEQ_SV
`define PCIE_PERFORMANCE_SEQ_SV

class pcie_performance_seq extends uvm_sequence #(pcie_transaction);
    `uvm_object_utils(pcie_performance_seq)
    
    int num_transactions = 10000;
    real throughput;
    time start_time, end_time;
    
    function new(string name = "pcie_performance_seq");
        super.new(name);
    endtask
    
    virtual task body();
        pcie_transaction tr;
        
        start_time = $time;
        
        repeat(num_transactions) begin
            tr = pcie_transaction::type_id::create("tr");
            start_item(tr);
            if(!tr.randomize() with {
                tx_valid == 1;
                tx_be == 4'hF;
            }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
        
        end_time = $time;
        throughput = (num_transactions * 32) / (end_time - start_time);
        
        `uvm_info("PERF", $sformatf("PCIe Throughput: %0.2f Gbps", throughput / 1e9), UVM_LOW)
    endtask
endclass

class pcie_max_payload_seq extends uvm_sequence #(pcie_transaction);
    `uvm_object_utils(pcie_max_payload_seq)
    
    int num_transactions = 1000;
    
    function new(string name = "pcie_max_payload_seq");
        super.new(name);
    endtask
    
    virtual task body();
        pcie_transaction tr;
        
        repeat(num_transactions) begin
            tr = pcie_transaction::type_id::create("tr");
            start_item(tr);
            if(!tr.randomize() with {
                tx_valid == 1;
                tx_be == 4'hF;
                tx_user.tlp_prefix == 1;
            }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class pcie_priority_seq extends uvm_sequence #(pcie_transaction);
    `uvm_object_utils(pcie_priority_seq)
    
    int high_priority_count = 1000;
    int low_priority_count = 1000;
    
    function new(string name = "pcie_priority_seq");
        super.new(name);
    endtask
    
    virtual task body();
        pcie_transaction tr;
        
        fork
            begin
                repeat(high_priority_count) begin
                    tr = pcie_transaction::type_id::create("tr");
                    start_item(tr);
                    if(!tr.randomize() with {
                        tx_valid == 1;
                        tx_user.traffic_class == 7;
                    }) begin
                        `uvm_error("SEQ", "Randomization failed")
                    end
                    finish_item(tr);
                end
            end
            begin
                repeat(low_priority_count) begin
                    tr = pcie_transaction::type_id::create("tr");
                    start_item(tr);
                    if(!tr.randomize() with {
                        tx_valid == 1;
                        tx_user.traffic_class == 0;
                    }) begin
                        `uvm_error("SEQ", "Randomization failed")
                    end
                    finish_item(tr);
                end
            end
        join
    endtask
endclass

`endif
