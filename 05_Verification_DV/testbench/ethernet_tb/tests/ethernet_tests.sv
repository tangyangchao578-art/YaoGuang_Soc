//-----------------------------------------------------------------------------
// File: ethernet_tests.sv
// Description: Ethernet Controller Test Cases
// Author: YaoGuang SoC DV Team
// Created: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef ETHERNET_TESTS_SV
`define ETHERNET_TESTS_SV

class ethernet_base_test extends uvm_test;
    `uvm_component_utils(ethernet_base_test)
    
    ethernet_env env;
    ethernet_config cfg;
    
    function new(string name = "ethernet_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        cfg = ethernet_config::type_id::create("cfg");
        cfg.agent_cfg = ethernet_agent_config::type_id::create("agent_cfg");
        if(!uvm_config_db #(virtual ethernet_if)::get(this, "", "ethernet_vif", cfg.agent_cfg.vif)) begin
            `uvm_error("TEST", "Cannot get ethernet_vif from config DB")
        end
        uvm_config_db #(ethernet_config)::set(this, "*", "ethernet_config", cfg);
        
        env = ethernet_env::type_id::create("env", this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        #1ms;
        phase.drop_objection(this);
    endtask
endclass

class ethernet_basic_test extends ethernet_base_test;
    `uvm_component_utils(ethernet_basic_test)
    
    function new(string name = "ethernet_basic_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        ethernet_basic_seq seq;
        
        phase.raise_objection(this);
        seq = ethernet_basic_seq::type_id::create("seq");
        seq.start(env.virt_seqr.ethernet_seqr);
        phase.drop_objection(this);
    endtask
endclass

class ethernet_error_test extends ethernet_base_test;
    `uvm_component_utils(ethernet_error_test)
    
    function new(string name = "ethernet_error_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        ethernet_crc_err_seq seq;
        
        phase.raise_objection(this);
        seq = ethernet_crc_err_seq::type_id::create("seq");
        seq.start(env.virt_seqr.ethernet_seqr);
        phase.drop_objection(this);
    endtask
endclass

class ethernet_performance_test extends ethernet_base_test;
    `uvm_component_utils(ethernet_performance_test)
    
    function new(string name = "ethernet_performance_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        ethernet_performance_seq seq;
        
        phase.raise_objection(this);
        seq = ethernet_performance_seq::type_id::create("seq");
        seq.start(env.virt_seqr.ethernet_seqr);
        phase.drop_objection(this);
    endtask
endclass

`endif
