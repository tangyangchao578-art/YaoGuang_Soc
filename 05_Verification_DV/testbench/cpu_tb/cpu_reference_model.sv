//-----------------------------------------------------------------------------
// File: cpu_reference_model.sv
// Description: CPU Subsystem reference model
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef CPU_REFERENCE_MODEL_SV
`define CPU_REFERENCE_MODEL_SV

class cpu_reference_model extends uvm_component;
    `uvm_component_utils(cpu_reference_model)

    uvm_tlm_analysis_fifo#(cpu_transaction) input_fifo;
    uvm_tlm_analysis_fifo#(cpu_transaction) output_fifo;

    bit [`MAX_ADDR_BITS-1:0] reg_file [`MAX_CORES][32];
    bit [`MAX_ADDR_BITS-1:0] program_counter [`MAX_CORES];
    bit [`MAX_ADDR_BITS-1:0] virtual_memory [`MAX_MEM_SIZE];
    bit [63:0] cycle_count;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        input_fifo = new("input_fifo", this);
        output_fifo = new("output_fifo", this);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        initialize_model();
    endfunction

    function void initialize_model();
        for(int i = 0; i < `MAX_CORES; i++) begin
            for(int j = 0; j < 32; j++) begin
                reg_file[i][j] = $urandom();
            end
            program_counter[i] = 'h0;
        end
        cycle_count = 0;
    endfunction

    task run_phase(uvm_phase phase);
        cpu_transaction tr;
        super.run_phase(phase);
        fork
            process_transactions();
        join_none
    endtask

    task process_transactions();
        forever begin
            input_fifo.get(tr);
            cycle_count++;
            execute_instruction(tr);
        end
    endtask

    function void execute_instruction(cpu_transaction tr);
        bit [63:0] result;
        bit [`MAX_ADDR_BITS-1:0] effective_addr;

        case(tr.opcode)
            OP_LOAD: begin
                effective_addr = tr.addr;
                result = virtual_memory[effective_addr >> 6];
                tr.data = result;
            end
            OP_STORE: begin
                effective_addr = tr.addr;
                virtual_memory[effective_addr >> 6] = tr.data;
            end
            OP_ALU: begin
                result = tr.data;
                tr.data = result;
            end
            OP_BRANCH: begin
                program_counter[0] = tr.addr;
            end
            default: begin
                tr.data = tr.data;
            end
        endcase
    endfunction
endclass

`define MAX_CORES 8
`endif
