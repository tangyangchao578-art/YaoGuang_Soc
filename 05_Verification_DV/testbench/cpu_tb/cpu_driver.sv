//-----------------------------------------------------------------------------
// File: cpu_driver.sv
// Description: CPU Subsystem driver
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef CPU_DRIVER_SV
`define CPU_DRIVER_SV

class cpu_driver extends uvm_driver#(cpu_transaction);
    `uvm_component_utils(cpu_driver)

    virtual cpu_if vif;
    cpu_config cfg;
    int transaction_count = 0;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual cpu_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("CPU_DRIVER", "Virtual interface not found")
        end
        cfg = cpu_config::type_id::create("cfg", this);
    endfunction

    task run_phase(uvm_phase phase);
        super.run_phase(phase);
        reset_driver();
        forever begin
            seq_item_port.get_next_item(req);
            drive_transaction(req);
            seq_item_port.item_done();
            transaction_count++;
            if(transaction_count % 1000 == 0) begin
                `uvm_info("CPU_DRIVER", $sformatf("Processed %0d transactions", transaction_count), UVM_LOW)
            end
        end
    endtask

    virtual task reset_driver();
        vif.valid <= 0;
        vif.ready <= 1;
        @(posedge vif.clk);
        #1;
    endtask

    virtual task drive_transaction(cpu_transaction tr);
        @(posedge vif.clk);
        vif.valid <= 1;
        vif.addr <= tr.addr;
        vif.data <= tr.data;
        vif.opcode <= tr.opcode;
        vif.size <= tr.size;

        while(!vif.ready) begin
            @(posedge vif.clk);
            #0.1;
        end

        @(posedge vif.clk);
        vif.valid <= 0;
    endtask
endclass

`endif
