//-----------------------------------------------------------------------------
// File: cpu_env.sv
// Description: CPU Subsystem verification environment
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef CPU_ENV_SV
`define CPU_ENV_SV

class cpu_env extends uvm_env;
    `uvm_component_utils(cpu_env)

    cpu_config cfg;
    cpu_agent agents[`MAX_CORES];
    cpu_scoreboard scoreboard;
    cpu_coverage coverage;
    cpu_reference_model ref_model;

    uvm_tlm_analysis_fifo#(cpu_transaction) scoreboard_fifo[`MAX_CORES];

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        cfg = cpu_config::type_id::create("cfg", this);
        uvm_config_db#(cpu_config)::set(this, "*", "cpu_config", cfg);

        for(int i = 0; i < cfg.num_cores; i++) begin
            agents[i] = cpu_agent::type_id::create($sformatf("agent_%0d", i), this);
            scoreboard_fifo[i] = new($sformatf("scoreboard_fifo_%0d", i), this);
        end

        scoreboard = cpu_scoreboard::type_id::create("scoreboard", this);
        coverage = cpu_coverage::type_id::create("coverage", this);
        ref_model = cpu_reference_model::type_id::create("ref_model", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        for(int i = 0; i < cfg.num_cores; i++) begin
            agents[i].ap.connect(scoreboard_fifo[i].analysis_export);
            scoreboard_fifo[i].connect(scoreboard.cpu_fifo);
        end
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
        `uvm_info("CPU_ENV", "=== CPU Verification Environment Report ===", UVM_LOW)
    endfunction
endclass

`endif
