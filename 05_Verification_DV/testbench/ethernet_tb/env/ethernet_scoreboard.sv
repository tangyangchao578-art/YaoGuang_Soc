//-----------------------------------------------------------------------------
// File: ethernet_scoreboard.sv
// Description: Ethernet Controller UVM Scoreboard
// Author: YaoGuang SoC DV Team
// Created: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef ETHERNET_SCOREBOARD_SV
`define ETHERNET_SCOREBOARD_SV

class ethernet_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(ethernet_scoreboard)
    
    uvm_analysis_export #(ethernet_transaction) item_collected_port;
    
    ethernet_transaction req_queue[$];
    ethernet_transaction rsp_queue[$];
    
    int passed_count = 0;
    int failed_count = 0;
    
    function new(string name = "ethernet_scoreboard", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        item_collected_port = new("item_collected_port", this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            ethernet_transaction tr;
            item_collected_port.peek(tr);
            process_transaction(tr);
        end
    endtask
    
    virtual protected function void process_transaction(ethernet_transaction tr);
        if(tr.tx_valid && tr.rx_valid) begin
            if(compare_transaction(tr)) begin
                `uvm_info("SCB", $sformatf("Ethernet Transaction PASSED: data=0x%0h", tr.tx_data), UVM_LOW)
                passed_count++;
            end else begin
                `uvm_error("SCB", $sformatf("Ethernet Transaction FAILED: data=0x%0h", tr.tx_data))
                failed_count++;
            end
        end
    endfunction
    
    virtual protected function bit compare_transaction(ethernet_transaction tr);
        return (tr.rx_data === tr.tx_data) && (tr.rx_valid === tr.tx_valid);
    endfunction
    
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("SCB_REPORT", $sformatf("=== Ethernet Scoreboard Report ==="), UVM_LOW)
        `uvm_info("SCB_REPORT", $sformatf("Passed: %0d", passed_count), UVM_LOW)
        `uvm_info("SCB_REPORT", $sformatf("Failed: %0d", failed_count), UVM_LOW)
        if(failed_count == 0) begin
            `uvm_info("SCB_REPORT", "ALL TESTS PASSED!", UVM_LOW)
        end else begin
            `uvm_error("SCB_REPORT", $sformatf("%0d TESTS FAILED!", failed_count))
        end
    endfunction
endclass

`endif
