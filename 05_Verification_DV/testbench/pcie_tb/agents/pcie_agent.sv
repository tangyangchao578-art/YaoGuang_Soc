//-----------------------------------------------------------------------------
// File: pcie_agent.sv
// Description: PCIe Controller UVM Agent
// Author: YaoGuang SoC DV Team
// Created: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef PCIE_AGENT_SV
`define PCIE_AGENT_SV

class pcie_agent_config extends uvm_object;
    `uvm_object_utils(pcie_agent_config)
    
    virtual pcie_if vif;
    bit is_active = 1;
    bit has_coverage = 1;
    
    function new(string name = "pcie_agent_config");
        super.new(name);
    endfunction
endclass

class pcie_agent extends uvm_agent;
    `uvm_component_utils(pcie_agent)
    
    pcie_agent_config  cfg;
    pcie_sequencer     seqr;
    pcie_driver        drv;
    pcie_monitor       monitor;
    
    function new(string name = "pcie_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if(!uvm_config_db #(pcie_agent_config)::get(this, "", "cfg", cfg)) begin
            `uvm_error("AGENT", "Cannot get pcie_agent_config from config DB")
        end
        
        monitor = pcie_monitor::type_id::create("monitor", this);
        
        if(cfg.is_active) begin
            seqr = pcie_sequencer::type_id::create("seqr", this);
            drv = pcie_driver::type_id::create("drv", this);
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

class pcie_sequencer extends uvm_sequencer #(pcie_transaction);
    `uvm_component_utils(pcie_sequencer)
    
    function new(string name = "pcie_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
endclass

class pcie_driver extends uvm_driver #(pcie_transaction);
    `uvm_component_utils(pcie_driver)
    
    virtual pcie_if vif;
    
    function new(string name = "pcie_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(req);
            drive_transaction(req);
            seq_item_port.item_done();
        end
    endtask
    
    virtual protected task drive_transaction(pcie_transaction tr);
        vif.drv_cb.tx_valid <= tr.tx_valid;
        vif.drv_cb.tx_data <= tr.tx_data;
        vif.drv_cb.tx_be <= tr.tx_be;
        vif.drv_cb.tx_addr <= tr.tx_addr;
        vif.drv_cb.tx_user <= tr.tx_user;
        @(vif.drv_cb);
    endtask
endclass

class pcie_monitor extends uvm_monitor;
    `uvm_component_utils(pcie_monitor)
    
    virtual pcie_if vif;
    uvm_analysis_port #(pcie_transaction) item_collected_port;
    
    function new(string name = "pcie_monitor", uvm_component parent = null);
        super.new(name, parent);
        item_collected_port = new("item_collected_port", this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            pcie_transaction tr;
            tr = new();
            collect_transaction(tr);
            item_collected_port.write(tr);
        end
    endtask
    
    virtual protected task collect_transaction(pcie_transaction tr);
        @(posedge vif.clk);
        tr.rx_valid = vif.mon_cb.rx_valid;
        tr.rx_data = vif.mon_cb.rx_data;
        tr.rx_be = vif.mon_cb.rx_be;
        tr.rx_addr = vif.mon_cb.rx_addr;
        tr.rx_user = vif.mon_cb.rx_user;
    endtask
endclass

`endif
