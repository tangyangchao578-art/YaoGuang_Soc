//-----------------------------------------------------------------------------
// File: l3_cache_env.sv
// Description: L3 Cache verification environment
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef L3_CACHE_ENV_SV
`define L3_CACHE_ENV_SV

class l3_cache_env extends uvm_env;
    `uvm_component_utils(l3_cache_env)

    l3_cache_config cfg;
    l3_cache_agent agent;
    l3_cache_scoreboard scoreboard;
    l3_cache_coverage coverage;
    l3_cache_reference_model ref_model;

    uvm_tlm_analysis_fifo#(l3_cache_transaction) scoreboard_fifo;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        cfg = l3_cache_config::type_id::create("cfg", this);
        uvm_config_db#(l3_cache_config)::set(this, "*", "l3_cache_config", cfg);

        agent = l3_cache_agent::type_id::create("agent", this);
        scoreboard_fifo = new("scoreboard_fifo", this);
        scoreboard = l3_cache_scoreboard::type_id::create("scoreboard", this);
        coverage = l3_cache_coverage::type_id::create("coverage", this);
        ref_model = l3_cache_reference_model::type_id::create("ref_model", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        agent.ap.connect(scoreboard_fifo.analysis_export);
        scoreboard_fifo.connect(scoreboard.l3_fifo);
    endfunction

    task run_phase(uvm_phase phase);
        super.run_phase(phase);
        phase.raise_objection(this);

        fork
            ref_model.run();
        join_none

        phase.drop_objection(this);
    endtask

    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("L3_CACHE_ENV", "=== L3 Cache Verification Environment Report ===", UVM_LOW)
    endfunction
endclass

`endif
