//-----------------------------------------------------------------------------
// File: pcie_error_seq.sv
// Description: PCIe Controller Error Test Sequence
// Author: YaoGuang SoC DV Team
// Created: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef PCIE_ERROR_SEQ_SV
`define PCIE_ERROR_SEQ_SV

class pcie_error_seq extends uvm_sequence #(pcie_transaction);
    `uvm_object_utils(pcie_error_seq)
    
    function new(string name = "pcie_error_seq");
        super.new(name);
    endtask
    
    virtual task body();
        pcie_transaction tr;
        
        tr = pcie_transaction::type_id::create("tr");
        start_item(tr);
        if(!tr.randomize() with {
            tx_valid == 0;
            tx_be == 0;
        }) begin
            `uvm_error("SEQ", "Randomization failed")
        end
        finish_item(tr);
    endtask
endclass

class pcie_parity_err_seq extends uvm_sequence #(pcie_transaction);
    `uvm_object_utils(pcie_parity_err_seq)
    
    function new(string name = "pcie_parity_err_seq");
        super.new(name);
    endtask
    
    virtual task body();
        pcie_transaction tr;
        
        for(int i = 0; i < 10; i++) begin
            tr = pcie_transaction::type_id::create("tr");
            start_item(tr);
            if(!tr.randomize() with {
                tx_valid == 1;
                tx_be == 0;
                tx_user.parity_error == 1;
            }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class pcie_unalign_seq extends uvm_sequence #(pcie_transaction);
    `uvm_object_utils(pcie_unalign_seq)
    
    function new(string name = "pcie_unalign_seq");
        super.new(name);
    endtask
    
    virtual task body();
        pcie_transaction tr;
        
        for(int i = 0; i < 10; i++) begin
            tr = pcie_transaction::type_id::create("tr");
            start_item(tr);
            if(!tr.randomize() with {
                tx_valid == 1;
                tx_addr[1:0] != 2'b00;
                tx_be inside {[1:15]};
            }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class pcie_timeout_seq extends uvm_sequence #(pcie_transaction);
    `uvm_object_utils(pcie_timeout_seq)
    
    int timeout_cycles = 10000;
    
    function new(string name = "pcie_timeout_seq");
        super.new(name);
    endtask
    
    virtual task body();
        pcie_transaction tr;
        
        tr = pcie_transaction::type_id::create("tr");
        start_item(tr);
        if(!tr.randomize() with {
            tx_valid == 1;
        }) begin
            `uvm_error("SEQ", "Randomization failed")
        end
        finish_item(tr);
        
        #(timeout_cycles * 1ns);
    endtask
endclass

class pcie_poison_tlp_seq extends uvm_sequence #(pcie_transaction);
    `uvm_object_utils(pcie_poison_tlp_seq)
    
    function new(string name = "pcie_poison_tlp_seq");
        super.new(name);
    endtask
    
    virtual task body();
        pcie_transaction tr;
        
        for(int i = 0; i < 5; i++) begin
            tr = pcie_transaction::type_id::create("tr");
            start_item(tr);
            if(!tr.randomize() with {
                tx_valid == 1;
                tx_user.poisoned_tlp == 1;
            }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

`endif
