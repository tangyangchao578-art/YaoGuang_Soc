//-----------------------------------------------------------------------------
// File: ethernet_env.sv
// Description: Ethernet Controller UVM Environment
// Author: YaoGuang SoC DV Team
// Created: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef ETHERNET_ENV_SV
`define ETHERNET_ENV_SV

class ethernet_env extends uvm_env;
    `uvm_component_utils(ethernet_env)
    
    ethernet_agent        ethernet_agt;
    ethernet_scoreboard   ethernet_scb;
    ethernet_coverage     ethernet_cov;
    ethernet_virtual_sequencer virt_seqr;
    
    uvm_tlm_analysis_fifo #(ethernet_transaction) scb_fifo;
    uvm_tlm_analysis_fifo #(ethernet_transaction) cov_fifo;
    
    ethernet_config       cfg;
    
    function new(string name = "ethernet_env", uvm_component parent = null);
        super.new(name, parent);
        scb_fifo = new("scb_fifo", this);
        cov_fifo = new("cov_fifo", this);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if(!uvm_config_db #(ethernet_config)::get(this, "", "ethernet_config", cfg)) begin
            `uvm_error("ENV", "Cannot get ethernet_config from config DB")
        end
        
        ethernet_agt = ethernet_agent::type_id::create("ethernet_agt", this);
        uvm_config_db #(ethernet_agent_config)::set(this, "ethernet_agt*", "cfg", cfg.agent_cfg);
        
        ethernet_scb = ethernet_scoreboard::type_id::create("ethernet_scb", this);
        ethernet_cov = ethernet_coverage::type_id::create("ethernet_cov", this);
        virt_seqr = ethernet_virtual_sequencer::type_id::create("virt_seqr", this);
        virt_seqr.cfg = cfg;
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        ethernet_agt.monitor.item_collected_port.connect(scb_fifo.analysis_export);
        ethernet_agt.monitor.item_collected_port.connect(cov_fifo.analysis_export);
        ethernet_scb.item_collected_port.connect(scb_fifo.get_export);
        ethernet_cov.item_collected_port.connect(cov_fifo.get_export);
        
        virt_seqr.ethernet_seqr = ethernet_agt.seqr;
    endfunction
endclass

`endif
