//-----------------------------------------------------------------------------
// File: cpu_reset_seq.sv
// Description: CPU reset test sequence
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef CPU_RESET_SEQ_SV
`define CPU_RESET_SEQ_SV

class cpu_reset_seq extends uvm_sequence#(cpu_transaction);
    `uvm_object_utils(cpu_reset_seq)

    cpu_config cfg;
    int reset_cycles = 10;

    function new(string name = "cpu_reset_seq");
        super.new(name);
    endfunction

    task body();
        cpu_transaction tr;

        `uvm_info("CPU_RESET_SEQ", "Starting reset test", UVM_LOW)

        fork
            test_power_on_reset(tr);
            test_warm_reset(tr);
            test_software_reset(tr);
        join

        `uvm_info("CPU_RESET_SEQ", "Completed reset test", UVM_LOW)
    endtask

    task test_power_on_reset(cpu_transaction tr);
        `uvm_info("CPU_RESET_SEQ", "Testing power-on reset", UVM_LOW)

        tr = cpu_transaction::type_id::create("tr_por_reset");
        start_item(tr);
        tr.opcode = OP_SYSTEM;
        tr.cache_op = CACHE_FLUSH;
        tr.cache_level = LEVEL_L1;
        tr.privilege = PRIV_KERNEL;
        tr.has_exception = 1;
        tr.exception_type = 8'hFF;
        finish_item(tr);

        #100;
    endtask

    task test_warm_reset(cpu_transaction tr);
        `uvm_info("CPU_RESET_SEQ", "Testing warm reset", UVM_LOW)

        for(int i = 0; i < 10; i++) begin
            tr = cpu_transaction::type_id::create("tr_warm_reset");
            start_item(tr);
            tr.opcode = OP_SYSTEM;
            tr.cache_op = CACHE_INVALIDATE;
            tr.cache_level = LEVEL_L2;
            tr.privilege = PRIV_KERNEL;
            finish_item(tr);
            #50;
        end
    endtask

    task test_software_reset(cpu_transaction tr);
        `uvm_info("CPU_RESET_SEQ", "Testing software reset", UVM_LOW)

        for(int i = 0; i < 5; i++) begin
            tr = cpu_transaction::type_id::create("tr_sw_reset");
            start_item(tr);
            tr.opcode = OP_SYSTEM;
            tr.cache_op = CACHE_FLUSH;
            tr.cache_level = LEVEL_L3;
            tr.privilege = PRIV_MONITOR;
            finish_item(tr);
            #100;
        end
    endtask
endclass

class cpu_reset_test extends uvm_test;
    `uvm_component_utils(cpu_reset_test)

    cpu_env env;
    cpu_config cfg;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = cpu_env::type_id::create("env", this);
        cfg = cpu_config::type_id::create("cfg", this);
    endfunction

    task run_phase(uvm_phase phase);
        cpu_reset_seq seq;

        phase.raise_objection(this);
        seq = cpu_reset_seq::type_id::create("seq");
        seq.start(env.agents[0].sequencer);
        phase.drop_objection(this);
    endtask
endclass

`endif
