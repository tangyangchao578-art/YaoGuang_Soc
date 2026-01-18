//-----------------------------------------------------------------------------
// File: ethernet_coverage.sv
// Description: Ethernet Controller UVM Coverage
// Author: YaoGuang SoC DV Team
// Created: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef ETHERNET_COVERAGE_SV
`define ETHERNET_COVERAGE_SV

class ethernet_coverage extends uvm_subscriber #(ethernet_transaction);
    `uvm_component_utils(ethernet_coverage)
    
    covergroup ethernet_cg;
        cp_tx_valid: coverpoint tx_valid { bins valid = {1}; bins invalid = {0}; }
        cp_rx_valid: coverpoint rx_valid { bins valid = {1}; bins invalid = {0}; }
        cp_tx_start: coverpoint tx_start { bins start = {1}; bins no_start = {0}; }
        cp_tx_end: coverpoint tx_end { bins end = {1}; bins no_end = {0}; }
        cp_tx_data: coverpoint tx_data { bins data_values[] = {64'h0000_0000_0000_0000, 64'hFFFF_FFFF_FFFF_FFFF, 64'hAAAA_AAAA_AAAA_AAAA, 64'h5555_5555_5555_5555}; }
        cross_tx: cross cp_tx_valid, cp_rx_valid, cp_tx_start, cp_tx_end;
    endgroup
    
    ethernet_transaction tx;
    
    function new(string name = "ethernet_coverage", uvm_component parent = null);
        super.new(name, parent);
        ethernet_cg = new();
    endfunction
    
    virtual function void write(ethernet_transaction t);
        tx = t;
        ethernet_cg.sample();
    endfunction
    
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("COV", $sformatf("Ethernet Coverage: %0.2f%%", ethernet_cg.get_coverage()), UVM_LOW)
    endfunction
endclass

`endif
