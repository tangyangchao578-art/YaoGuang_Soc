//-----------------------------------------------------------------------------
// File: cpu_instruction_seq.sv
// Description: CPU instruction execution test sequence
// Test Points: CPU-CORE-001 (指令执行正确性)
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef CPU_INSTRUCTION_SEQ_SV
`define CPU_INSTRUCTION_SEQ_SV

class cpu_instruction_seq extends uvm_sequence#(cpu_transaction);
    `uvm_object_utils(cpu_instruction_seq)

    cpu_config cfg;
    int num_transactions = 1000;

    function new(string name = "cpu_instruction_seq");
        super.new(name);
    endfunction

    task body();
        cpu_transaction tr;

        `uvm_info("CPU_INSTRUCTION_SEQ", "Starting instruction execution test", UVM_LOW)

        for(int i = 0; i < num_transactions; i++) begin
            tr = cpu_transaction::type_id::create("tr");
            start_item(tr);

            randomize_tr(tr, i);
            finish_item(tr);

            if(i % 100 == 0) begin
                `uvm_info("CPU_INSTRUCTION_SEQ", $sformatf("Progress: %0d/%0d", i, num_transactions), UVM_LOW)
            end
        end

        `uvm_info("CPU_INSTRUCTION_SEQ", "Completed instruction execution test", UVM_LOW)
    endtask

    virtual function void randomize_tr(cpu_transaction tr, int idx);
        bit [7:0] opcode_selection;

        opcode_selection = $urandom_range(0, 7);

        case(opcode_selection)
            0: tr.opcode = OP_LOAD;
            1: tr.opcode = OP_STORE;
            2: tr.opcode = OP_BRANCH;
            3: tr.opcode = OP_ALU;
            4: tr.opcode = OP_FPU;
            5: tr.opcode = OP_SIMD;
            6: tr.opcode = OP_SYSTEM;
            7: tr.opcode = OP_NOP;
        endcase

        tr.addr = $urandom_range(0, `MAX_MEM_SIZE * 64);
        tr.data = $urandom();
        tr.size = $urandom_range(1, 8);
        tr.privilege = cpu_privilege_t'($urandom_range(0, 3));
        tr.cache_op = CACHE_NONE;
        tr.cache_level = LEVEL_L1;
        tr.mmu_state = $urandom_range(0, 1);
        tr.has_exception = 0;
        tr.exception_type = 0;
    endfunction
endclass

class cpu_instruction_test extends uvm_test;
    `uvm_component_utils(cpu_instruction_test)

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
        cpu_instruction_seq seq;

        phase.raise_objection(this);
        seq = cpu_instruction_seq::type_id::create("seq");
        seq.start(env.agents[0].sequencer);
        phase.drop_objection(this);
    endtask
endclass

`endif
