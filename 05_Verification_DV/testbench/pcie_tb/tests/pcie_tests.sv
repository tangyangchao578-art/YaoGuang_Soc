//-----------------------------------------------------------------------------
// File: pcie_tests.sv
// Description: PCIe Controller Test Cases
// Author: YaoGuang SoC DV Team
// Created: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef PCIE_TESTS_SV
`define PCIE_TESTS_SV

class pcie_base_test extends uvm_test;
    `uvm_component_utils(pcie_base_test)
    
    pcie_env env;
    pcie_config cfg;
    
    function new(string name = "pcie_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        cfg = pcie_config::type_id::create("cfg");
        cfg.agent_cfg = pcie_agent_config::type_id::create("agent_cfg");
        if(!uvm_config_db #(virtual pcie_if)::get(this, "", "pcie_vif", cfg.agent_cfg.vif)) begin
            `uvm_error("TEST", "Cannot get pcie_vif from config DB")
        end
        uvm_config_db #(pcie_config)::set(this, "*", "pcie_config", cfg);
        
        env = pcie_env::type_id::create("env", this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        #1ms;
        phase.drop_objection(this);
    endtask
endclass

class pcie_basic_test extends pcie_base_test;
    `uvm_component_utils(pcie_basic_test)
    
    function new(string name = "pcie_basic_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        pcie_basic_seq seq;
        
        phase.raise_objection(this);
        seq = pcie_basic_seq::type_id::create("seq");
        seq.start(env.virt_seqr.pcie_seqr);
        phase.drop_objection(this);
    endtask
endclass

class pcie_cfg_space_test extends pcie_base_test;
    `uvm_component_utils(pcie_cfg_space_test)
    
    function new(string name = "pcie_cfg_space_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        pcie_cfg_space_seq seq;
        
        phase.raise_objection(this);
        seq = pcie_cfg_space_seq::type_id::create("seq");
        seq.start(env.virt_seqr.pcie_seqr);
        phase.drop_objection(this);
    endtask
endclass

class pcie_error_test extends pcie_base_test;
    `uvm_component_utils(pcie_error_test)
    
    function new(string name = "pcie_error_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        pcie_error_seq seq;
        
        phase.raise_objection(this);
        seq = pcie_error_seq::type_id::create("seq");
        seq.start(env.virt_seqr.pcie_seqr);
        phase.drop_objection(this);
    endtask
endclass

class pcie_performance_test extends pcie_base_test;
    `uvm_component_utils(pcie_performance_test)
    
    function new(string name = "pcie_performance_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        pcie_performance_seq seq;
        
        phase.raise_objection(this);
        seq = pcie_performance_seq::type_id::create("seq");
        seq.start(env.virt_seqr.pcie_seqr);
        phase.drop_objection(this);
    endtask
endclass

`endif
