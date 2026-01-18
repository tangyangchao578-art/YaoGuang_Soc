//-----------------------------------------------------------------------------
// File: cpu_interrupt_seq.sv
// Description: CPU interrupt test sequence
// Test Points: CPU-GIC-001 ~ CPU-GIC-003
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef CPU_INTERRUPT_SEQ_SV
`define CPU_INTERRUPT_SEQ_SV

class cpu_interrupt_seq extends uvm_sequence#(cpu_transaction);
    `uvm_object_utils(cpu_interrupt_seq)

    cpu_config cfg;
    int num_interrupts = 200;

    function new(string name = "cpu_interrupt_seq");
        super.new(name);
    endfunction

    task body();
        cpu_transaction tr;

        `uvm_info("CPU_INTERRUPT_SEQ", "Starting interrupt test", UVM_LOW)

        fork
            test_interrupt_enable(tr);
            test_interrupt_priority(tr);
            test_interrupt_nesting(tr);
        join

        `uvm_info("CPU_INTERRUPT_SEQ", "Completed interrupt test", UVM_LOW)
    endtask

    task test_interrupt_enable(cpu_transaction tr);
        for(int i = 0; i < num_interrupts/3; i++) begin
            tr = cpu_transaction::type_id::create("tr_irq_enable");
            start_item(tr);
            randomize_irq_enable(tr);
            finish_item(tr);
            #100;
        end
    endtask

    task test_interrupt_priority(cpu_transaction tr);
        for(int i = 0; i < num_interrupts/3; i++) begin
            tr = cpu_transaction::type_id::create("tr_irq_prio");
            start_item(tr);
            randomize_irq_priority(tr);
            finish_item(tr);
            #100;
        end
    endtask

    task test_interrupt_nesting(cpu_transaction tr);
        for(int i = 0; i < num_interrupts/3; i++) begin
            tr = cpu_transaction::type_id::create("tr_irq_nest");
            start_item(tr);
            randomize_irq_nesting(tr);
            finish_item(tr);
            #100;
        end
    endtask

    virtual function void randomize_irq_enable(cpu_transaction tr);
        tr.opcode = OP_SYSTEM;
        tr.irq_enabled = 1;
        tr.irq_type = irq_type_t'($urandom_range(0, 2));
        tr.irq_prio = $urandom_range(0, 255);
        tr.cache_op = CACHE_NONE;
        tr.privilege = PRIV_KERNEL;
        tr.has_exception = 1;
        tr.exception_type = 8'h01;
    endfunction

    virtual function void randomize_irq_priority(cpu_transaction tr);
        tr.opcode = OP_SYSTEM;
        tr.irq_enabled = $urandom_range(0, 1);
        tr.irq_type = irq_type_t'($urandom_range(0, 2));
        tr.irq_prio = $urandom_range(0, 255);
        tr.cache_op = CACHE_NONE;
        tr.privilege = PRIV_KERNEL;
        tr.has_exception = 0;
    endfunction

    virtual function void randomize_irq_nesting(cpu_transaction tr);
        tr.opcode = OP_SYSTEM;
        tr.irq_enabled = 1;
        tr.irq_type = IRQ_SPI;
        tr.irq_prio = $urandom_range(0, 63);
        tr.cache_op = CACHE_NONE;
        tr.privilege = PRIV_KERNEL;
        tr.has_exception = 1;
        tr.exception_type = 8'h02;
    endfunction
endclass

class cpu_interrupt_test extends uvm_test;
    `uvm_component_utils(cpu_interrupt_test)

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
        cpu_interrupt_seq seq;

        phase.raise_objection(this);
        seq = cpu_interrupt_seq::type_id::create("seq");
        seq.start(env.agents[0].sequencer);
        phase.drop_objection(this);
    endtask
endclass

`endif
