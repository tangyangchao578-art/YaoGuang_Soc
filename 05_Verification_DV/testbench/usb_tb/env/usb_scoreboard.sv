//-----------------------------------------------------------------------------
// File: usb_scoreboard.sv
// Description: USB Controller UVM Scoreboard
//-----------------------------------------------------------------------------
`ifndef USB_SCOREBOARD_SV
`define USB_SCOREBOARD_SV

class usb_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(usb_scoreboard)
    
    uvm_analysis_export #(usb_transaction) item_collected_port;
    
    int passed_count = 0;
    int failed_count = 0;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        item_collected_port = new("item_collected_port", this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            usb_transaction tr;
            item_collected_port.peek(tr);
            process_transaction(tr);
        end
    endtask
    
    virtual protected function void process_transaction(usb_transaction tr);
        if(tr.tx_valid && tr.rx_valid) begin
            if(compare_transaction(tr)) begin
                `uvm_info("SCB", $sformatf("USB Transaction PASSED"), UVM_LOW)
                passed_count++;
            end else begin
                `uvm_error("SCB", $sformatf("USB Transaction FAILED"))
                failed_count++;
            end
        end
    endfunction
    
    virtual protected function bit compare_transaction(usb_transaction tr);
        return (tr.rx_data === tr.tx_data);
    endfunction
    
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("SCB_REPORT", $sformatf("=== USB Scoreboard Report ==="), UVM_LOW)
        `uvm_info("SCB_REPORT", $sformatf("Passed: %0d", passed_count), UVM_LOW)
        `uvm_info("SCB_REPORT", $sformatf("Failed: %0d", failed_count), UVM_LOW)
    endfunction
endclass

`endif
