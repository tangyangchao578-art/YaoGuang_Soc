//-----------------------------------------------------------------------------
// File: pcie_coverage.sv
// Description: PCIe Controller UVM Coverage
// Author: YaoGuang SoC DV Team
// Created: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef PCIE_COVERAGE_SV
`define PCIE_COVERAGE_SV

class pcie_coverage extends uvm_subscriber #(pcie_transaction);
    `uvm_component_utils(pcie_coverage)
    
    covergroup pcie_cg;
        cp_tx_valid: coverpoint tx_valid { bins valid = {1}; bins invalid = {0}; }
        cp_rx_valid: coverpoint rx_valid { bins valid = {1}; bins invalid = {0}; }
        cp_tx_be: coverpoint tx_be {
            bins byte_enables[] = {[0:15]};
            illegal_bins invalid = {16'h0000};
        }
        cp_tx_addr: coverpoint tx_addr {
            bins addr_ranges[] = {
                [32'h0000_0000:32'h0FFF_FFFF],
                [32'h1000_0000:32'h1FFF_FFFF],
                [32'h2000_0000:32'h2FFF_FFFF]
            };
        }
        cp_tx_data: coverpoint tx_data { bins data_values[] = {32'h0000_0000, 32'hFFFF_FFFF, 32'hAAAA_AAAA, 32'h5555_5555}; }
        cross_tx: cross cp_tx_valid, cp_rx_valid;
    endgroup
    
    pcie_transaction tx;
    
    function new(string name = "pcie_coverage", uvm_component parent = null);
        super.new(name, parent);
        pcie_cg = new();
    endfunction
    
    virtual function void write(pcie_transaction t);
        tx = t;
        pcie_cg.sample();
    endfunction
    
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("COV", $sformatf("PCIe Coverage: %0.2f%%", pcie_cg.get_coverage()), UVM_LOW)
    endfunction
endclass

`endif
