//-----------------------------------------------------------------------------
// Safety Island Driver
// YaoGuang SoC ASIL-D Safety Module Verification
//-----------------------------------------------------------------------------
`ifndef SAFETY_ISLAND_DRIVER_SV
`define SAFETY_ISLAND_DRIVER_SV

class safety_island_driver extends uvm_driver#(safety_island_transaction);
    `uvm_component_utils(safety_island_driver)
    
    virtual safety_island_if  vif;
    
    function new(string name = "safety_island_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual safety_island_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("DRV", "Cannot get vif from config_db")
        end
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        super.run_phase(phase);
        
        forever begin
            seq_item_port.get_next_item(req);
            drive_transaction(req);
            seq_item_port.item_done();
        end
    endtask
    
    virtual protected task drive_transaction(safety_island_transaction tr);
        vif.drv_cb.valid <= 1'b1;
        vif.drv_cb.opcode <= tr.opcode;
        vif.drv_cb.data <= tr.data;
        vif.drv_cb.addr <= tr.addr;
        vif.drv_cb.id <= tr.id;
        
        @(vif.drv_cb);
        
        while(!vif.drv_cb.ready) begin
            @(vif.drv_cb);
        end
        
        vif.drv_cb.valid <= 1'b0;
    endtask
endclass

`endif
