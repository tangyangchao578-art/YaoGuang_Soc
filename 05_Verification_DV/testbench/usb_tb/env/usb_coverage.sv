//-----------------------------------------------------------------------------
// File: usb_coverage.sv
// Description: USB Controller UVM Coverage
//-----------------------------------------------------------------------------
`ifndef USB_COVERAGE_SV
`define USB_COVERAGE_SV

class usb_coverage extends uvm_subscriber #(usb_transaction);
    `uvm_component_utils(usb_coverage)
    
    covergroup usb_cg;
        cp_tx_valid: coverpoint tx_valid { bins valid = {1}; bins invalid = {0}; }
        cp_rx_valid: coverpoint rx_valid { bins valid = {1}; bins invalid = {0}; }
        cp_tx_data: coverpoint tx_data { bins data_values[] = {8'h00, 8'hFF, 8'h55, 8'hAA}; }
        cross_tx: cross cp_tx_valid, cp_rx_valid;
    endgroup
    
    usb_transaction tx;
    
    function new(string name = "usb_coverage", uvm_component parent = null);
        super.new(name, parent);
        usb_cg = new();
    endfunction
    
    virtual function void write(usb_transaction t);
        tx = t;
        usb_cg.sample();
    endfunction
    
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("COV", $sformatf("USB Coverage: %0.2f%%", usb_cg.get_coverage()), UVM_LOW)
    endfunction
endclass

`endif
