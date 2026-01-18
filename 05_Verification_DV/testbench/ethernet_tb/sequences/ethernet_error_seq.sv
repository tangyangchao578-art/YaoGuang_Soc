//-----------------------------------------------------------------------------
// File: ethernet_error_seq.sv
// Description: Ethernet Controller Error Test Sequence
// Author: YaoGuang SoC DV Team
// Created: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef ETHERNET_ERROR_SEQ_SV
`define ETHERNET_ERROR_SEQ_SV

class ethernet_crc_err_seq extends uvm_sequence #(ethernet_transaction);
    `uvm_object_utils(ethernet_crc_err_seq)
    
    function new(string name = "ethernet_crc_err_seq");
        super.new(name);
    endtask
    
    virtual task body();
        for(int i = 0; i < 10; i++) begin
            ethernet_transaction tr;
            tr = ethernet_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with {
                tx_valid == 1;
                tx_data[7:0] == 8'h00;
            }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class ethernet_frag_seq extends uvm_sequence #(ethernet_transaction);
    `uvm_object_utils(ethernet_frag_seq)
    
    function new(string name = "ethernet_frag_seq");
        super.new(name);
    endtask
    
    virtual task body();
        for(int i = 0; i < 10; i++) begin
            ethernet_transaction tr;
            tr = ethernet_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with {
                tx_valid == 1;
                tx_start == 0;
                tx_end == 1;
            }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class ethernet_jumbo_seq extends uvm_sequence #(ethernet_transaction);
    `uvm_object_utils(ethernet_jumbo_seq)
    
    int frame_size = 9000;
    
    function new(string name = "ethernet_jumbo_seq");
        super.new(name);
    endtask
    
    virtual task body();
        for(int i = 0; i < 10; i++) begin
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
