//-----------------------------------------------------------------------------
// File: pcie_env.sv
// Description: PCIe Controller UVM Environment
// Author: YaoGuang SoC DV Team
// Created: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef PCIE_ENV_SV
`define PCIE_ENV_SV

class pcie_env extends uvm_env;
    `uvm_component_utils(pcie_env)
    
    pcie_agent        pcie_agt;
    pcie_scoreboard   pcie_scb;
    pcie_coverage     pcie_cov;
    pcie_virtual_sequencer virt_seqr;
    
    uvm_tlm_analysis_fifo #(pcie_transaction) scb_fifo;
    uvm_tlm_analysis_fifo #(pcie_transaction) cov_fifo;
    
    pcie_config       cfg;
    
    function new(string name = "pcie_env", uvm_component parent = null);
        super.new(name, parent);
        scb_fifo = new("scb_fifo", this);
        cov_fifo = new("cov_fifo", this);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if(!uvm_config_db #(pcie_config)::get(this, "", "pcie_config", cfg)) begin
            `uvm_error("ENV", "Cannot get pcie_config from config DB")
        end
        
        pcie_agt = pcie_agent::type_id::create("pcie_agt", this);
        uvm_config_db #(pcie_agent_config)::set(this, "pcie_agt*", "cfg", cfg.agent_cfg);
        
        pcie_scb = pcie_scoreboard::type_id::create("pcie_scb", this);
        pcie_cov = pcie_coverage::type_id::create("pcie_cov", this);
        virt_seqr = pcie_virtual_sequencer::type_id::create("virt_seqr", this);
        virt_seqr.cfg = cfg;
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        pcie_agt.monitor.item_collected_port.connect(scb_fifo.analysis_export);
        pcie_agt.monitor.item_collected_port.connect(cov_fifo.analysis_export);
        pcie_scb.item_collected_port.connect(scb_fifo.get_export);
        pcie_cov.item_collected_port.connect(cov_fifo.get_export);
        
        virt_seqr.pcie_seqr = pcie_agt.seqr;
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        fork
            forever begin
                pcie_transaction tr;
                if(scb_fifo.try_get(tr)) begin
                    pcie_scb.check_transaction(tr);
                end
                #1ns;
            end
        join_none
        phase.drop_objection(this);
    endtask
endclass

`endif
