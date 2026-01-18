//-----------------------------------------------------------------------------
// File: pcie_basic_seq.sv
// Description: PCIe Controller Basic Test Sequence
// Author: YaoGuang SoC DV Team
// Created: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef PCIE_BASIC_SEQ_SV
`define PCIE_BASIC_SEQ_SV

class pcie_basic_seq extends uvm_sequence #(pcie_transaction);
    `uvm_object_utils(pcie_basic_seq)
    
    int num_transactions = 100;
    
    function new(string name = "pcie_basic_seq");
        super.new(name);
    endtask
    
    virtual task body();
        repeat(num_transactions) begin
            pcie_transaction tr;
            tr = pcie_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with {
                tx_valid == 1;
                tx_be != 0;
            }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class pcie_cfg_space_seq extends uvm_sequence #(pcie_transaction);
    `uvm_object_utils(pcie_cfg_space_seq)
    
    function new(string name = "pcie_cfg_space_seq");
        super.new(name);
    endtask
    
    virtual task body();
        pcie_transaction tr;
        int cfg_addr;
        
        for(int i = 0; i < 256; i++) begin
            tr = pcie_transaction::type_id::create("tr");
            cfg_addr = 32'h8000_0000 | (i << 8);
            start_item(tr);
            if(!tr.randomize() with {
                tx_valid == 1;
                tx_addr == cfg_addr;
                tx_be == 4'hF;
            }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class pcie_mem_access_seq extends uvm_sequence #(pcie_transaction);
    `uvm_object_utils(pcie_mem_access_seq)
    
    function new(string name = "pcie_mem_access_seq");
        super.new(name);
    endtask
    
    virtual task body();
        pcie_transaction tr;
        
        for(int i = 0; i < 1000; i++) begin
            tr = pcie_transaction::type_id::create("tr");
            start_item(tr);
            if(!tr.randomize() with {
                tx_valid == 1;
                tx_addr inside {[32'h0000_0000:32'h0FFF_FFFF]};
                tx_be inside {[1:15]};
            }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class pcie_io_space_seq extends uvm_sequence #(pcie_transaction);
    `uvm_object_utils(pcie_io_space_seq)
    
    function new(string name = "pcie_io_space_seq");
        super.new(name);
    endtask
    
    virtual task body();
        pcie_transaction tr;
        
        for(int i = 0; i < 100; i++) begin
            tr = pcie_transaction::type_id::create("tr");
            start_item(tr);
            if(!tr.randomize() with {
                tx_valid == 1;
                tx_addr inside {[32'h0000_0000:32'h000F_FFFF]};
                tx_be inside {[1:3]};
            }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class pcie_burst_seq extends uvm_sequence #(pcie_transaction);
    `uvm_object_utils(pcie_burst_seq)
    
    int burst_length = 16;
    
    function new(string name = "pcie_burst_seq");
        super.new(name);
    endtask
    
    virtual task body();
        pcie_transaction tr;
        bit [31:0] base_addr = 32'h0010_0000;
        
        for(int i = 0; i < burst_length; i++) begin
            tr = pcie_transaction::type_id::create("tr");
            start_item(tr);
            if(!tr.randomize() with {
                tx_valid == 1;
                tx_addr == base_addr + (i * 4);
                tx_be == 4'hF;
            }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

`endif
