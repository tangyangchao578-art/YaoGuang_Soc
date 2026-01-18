//-----------------------------------------------------------------------------
// File: usb_agent.sv
// Description: USB Controller UVM Agent
//-----------------------------------------------------------------------------
`ifndef USB_AGENT_SV
`define USB_AGENT_SV

class usb_agent_config extends uvm_object;
    `uvm_object_utils(usb_agent_config)
    
    virtual usb_if vif;
    bit is_active = 1;
    
    function new(string name = "usb_agent_config");
        super.new(name);
    endfunction
endclass

class usb_agent extends uvm_agent;
    `uvm_component_utils(usb_agent)
    
    usb_agent_config  cfg;
    usb_sequencer     seqr;
    usb_driver        drv;
    usb_monitor       monitor;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if(!uvm_config_db #(usb_agent_config)::get(this, "", "cfg", cfg)) begin
            `uvm_error("AGENT", "Cannot get usb_agent_config")
        end
        
        monitor = usb_monitor::type_id::create("monitor", this);
        
        if(cfg.is_active) begin
            seqr = usb_sequencer::type_id::create("seqr", this);
            drv = usb_driver::type_id::create("drv", this);
        end
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        if(cfg.is_active) begin
            drv.seq_item_port.connect(seqr.seq_item_export);
        end
        monitor.vif = cfg.vif;
        drv.vif = cfg.vif;
    endfunction
endclass

class usb_sequencer extends uvm_sequencer #(usb_transaction);
    `uvm_component_utils(usb_sequencer)
    
    function new(string name = "usb_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
endclass

class usb_driver extends uvm_driver #(usb_transaction);
    `uvm_component_utils(usb_driver)
    
    virtual usb_if vif;
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(req);
            drive_transaction(req);
            seq_item_port.item_done();
        end
    endtask
    
    virtual protected task drive_transaction(usb_transaction tr);
        vif.drv_cb.tx_valid <= tr.tx_valid;
        vif.drv_cb.tx_data <= tr.tx_data;
        @(vif.drv_cb);
    endtask
endclass

class usb_monitor extends uvm_monitor;
    `uvm_component_utils(usb_monitor)
    
    virtual usb_if vif;
    uvm_analysis_port #(usb_transaction) item_collected_port;
    
    function new(string name = "usb_monitor", uvm_component parent = null);
        super.new(name, parent);
        item_collected_port = new("item_collected_port", this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            usb_transaction tr;
            tr = new();
            collect_transaction(tr);
            item_collected_port.write(tr);
        end
    endtask
    
    virtual protected task collect_transaction(usb_transaction tr);
        @(posedge vif.clk);
        tr.rx_valid = vif.mon_cb.rx_valid;
        tr.rx_data = vif.mon_cb.rx_data;
    endtask
endclass

`endif
