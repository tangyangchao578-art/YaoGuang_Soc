//-----------------------------------------------------------------------------
// File: ethernet_basic_seq.sv
// Description: Ethernet Controller Basic Test Sequence
// Author: YaoGuang SoC DV Team
// Created: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef ETHERNET_BASIC_SEQ_SV
`define ETHERNET_BASIC_SEQ_SV

class ethernet_basic_seq extends uvm_sequence #(ethernet_transaction);
    `uvm_object_utils(ethernet_basic_seq)
    
    int num_transactions = 100;
    
    function new(string name = "ethernet_basic_seq");
        super.new(name);
    endtask
    
    virtual task body();
        repeat(num_transactions) begin
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

class ethernet_frame_seq extends uvm_sequence #(ethernet_transaction);
    `uvm_object_utils(ethernet_frame_seq)
    
    int frame_size = 1500;
    int num_frames = 50;
    
    function new(string name = "ethernet_frame_seq");
        super.new(name);
    endtask
    
    virtual task body();
        for(int i = 0; i < num_frames; i++) begin
            ethernet_transaction tr;
            tr = ethernet_transaction::type_id::create("tr");
            
            start_item(tr);
            if(!tr.randomize() with {
                tx_valid == 1;
                tx_start == (i == 0);
                tx_end == (i == num_frames - 1);
            }) begin
                `uvm_error("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class ethernet_mdio_seq extends uvm_sequence #(ethernet_transaction);
    `uvm_object_utils(ethernet_mdio_seq)
    
    function new(string name = "ethernet_mdio_seq");
        super.new(name);
    endtask
    
    virtual task body();
        for(int phy_addr = 0; phy_addr < 32; phy_addr++) begin
            for(int reg_addr = 0; reg_addr < 32; reg_addr++) begin
                ethernet_transaction tr;
                tr = ethernet_transaction::type_id::create("tr");
                
                start_item(tr);
                if(!tr.randomize() with {
                    tx_valid == 1;
                    tx_data[31:16] == {phy_addr[4:0], reg_addr[4:0]};
                }) begin
                    `uvm_error("SEQ", "Randomization failed")
                end
                finish_item(tr);
            end
        end
    endtask
endclass

`endif
