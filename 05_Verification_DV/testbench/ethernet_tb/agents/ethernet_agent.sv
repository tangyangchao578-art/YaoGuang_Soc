//-----------------------------------------------------------------------------
// File: ethernet_agent.sv
// Description: Ethernet Controller UVM Agent
// Author: YaoGuang SoC DV Team
// Created: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef ETHERNET_AGENT_SV
`define ETHERNET_AGENT_SV

class ethernet_agent_config extends uvm_object;
    `uvm_object_utils(ethernet_agent_config)
    
    virtual ethernet_if vif;
    bit is_active = 1;
    bit has_coverage = 1;
    
    function new(string name = "ethernet_agent_config");
        super.new(name);
    endfunction
endclass

class ethernet_agent extends uvm_agent;
    `uvm_component_utils(ethernet_agent)
    
    ethernet_agent_config  cfg;
    ethernet_sequencer     seqr;
    ethernet_driver        drv;
    ethernet_monitor       monitor;
    
    function new(string name = "ethernet_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function voidm_phase phase);
        super.build_phase(phase);
        
        if(!uvm_config_db #( build_phase(uvethernet_agent_config)::get(this, "", "cfg", cfg)) begin
            `uvm_error("AGENT", "Cannot get ethernet_agent_config from config DB")
        end
        
        monitor = ethernet_monitor::type_id::create("monitor", this);
        
        if(cfg.is_active) begin
            seqr = ethernet_sequencer::type_id::create("seqr", this);
            drv = ethernet_driver::type_id::create("drv", this);
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

class ethernet_sequencer extends uvm_sequencer #(ethernet_transaction);
    `uvm_component_utils(ethernet_sequencer)
    
    function new(string name = "ethernet_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
endclass

class ethernet_driver extends uvm_driver #(ethernet_transaction);
    `uvm_component_utils(ethernet_driver)
    
    virtual ethernet_if vif;
    
    function new(string name = "ethernet_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(req);
            drive_transaction(req);
            seq_item_port.item_done();
        end
    endtask
    
    virtual protected task drive_transaction(ethernet_transaction tr);
        vif.drv_cb.tx_valid <= tr.tx_valid;
        vif.drv_cb.tx_data <= tr.tx_data;
        vif.drv_cb.tx_start <= tr.tx_start;
        vif.drv_cb.tx_end <= tr.tx_end;
        @(vif.drv_cb);
    endtask
endclass

class ethernet_monitor extends uvm_monitor;
    `uvm_component_utils(ethernet_monitor)
    
    virtual ethernet_if vif;
    uvm_analysis_port #(ethernet_transaction) item_collected_port;
    
    function new(string name = "ethernet_monitor", uvm_component parent = null);
        super.new(name, parent);
        item_collected_port = new("item_collected_port", this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            ethernet_transaction tr;
            tr = new();
            collect_transaction(tr);
            item_collected_port.write(tr);
        end
    endtask
    
    virtual protected task collect_transaction(ethernet_transaction tr);
        @(posedge vif.clk);
        tr.rx_valid = vif.mon_cb.rx_valid;
        tr.rx_data = vif.mon_cb.rx_data;
        tr.rx_start = vif.mon_cb.rx_start;
        tr.rx_end = vif.mon_cb.rx_end;
    endtask
endclass

`endif
