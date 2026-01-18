//-----------------------------------------------------------------------------
// File: cpu_transaction.sv
// Description: CPU Subsystem transaction definition
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef CPU_TRANSACTION_SV
`define CPU_TRANSACTION_SV

`define MAX_ADDR_BITS 64
`define MAX_DATA_BITS 64
`define MAX_MEM_SIZE 1024

typedef enum bit [7:0] {
    OP_LOAD = 8'h01,
    OP_STORE = 8'h02,
    OP_BRANCH = 8'h03,
    OP_ALU = 8'h04,
    OP_FPU = 8'h05,
    OP_SIMD = 8'h06,
    OP_SYSTEM = 8'h07,
    OP бар    OP_NOP = 8'h00
} cpu_opcode_t;

typedef enum bit [1:0] {
    PRIV_KERNEL = 2'b00,
    PRIV_USER = 2'b01,
    PRIV_HYPERVISOR = 2'b10,
    PRIV_MONITOR = 2'b11
} cpu_privilege_t;

typedef enum bit [2:0] {
    CACHE_NONE = 3'b000,
    CACHE_CLEAN = 3'b001,
    CACHE_INVALIDATE = 3'b010,
    CACHE_FLUSH = 3'b011,
    CACHE_WRITEALLOCATE = 3'b100,
    CACHE_NOALLOCATE = 3'b101
} cpu_cache_op_t;

typedef enum bit [1:0] {
    LEVEL_L1 = 2'b00,
    LEVEL_L2 = 2'b01,
    LEVEL_L3 = 2'b10
} cache_level_t;

typedef enum bit [2:0] {
    STALL_NONE = 3'b000,
    STALL_CACHE_MISS = 3'b001,
    STALL_TLB_MISS = 3'b010,
    STALL_DEPENDENCY = 3'b011,
    STALL_RESOURCE = 3'b100,
    STALL_BRANCH_MISPREDICT = 3'b101
} stall_reason_t;

typedef enum bit [1:0] {
    IRQ_SGI = 2'b00,
    IRQ_PPI = 2'b01,
    IRQ_SPI = 2'b10
} irq_type_t;

class cpu_transaction extends uvm_sequence_item;
    `uvm_object_utils(cpu_transaction)

    rand cpu_opcode_t opcode;
    rand bit [`MAX_ADDR_BITS-1:0] addr;
    rand bit [`MAX_DATA_BITS-1:0] data;
    rand bit [3:0] size;
    rand bit burst;
    rand bit [3:0] length;
    rand cpu_privilege_t privilege;
    rand bit has_exception;
    rand bit [7:0] exception_type;
    rand cpu_cache_op_t cache_op;
    rand cache_level_t cache_level;
    rand bit mmu_state;
    rand bit [7:0] irq_type;
    rand bit [7:0] irq_prio;
    rand bit irq_enabled;
    rand bit [7:0] stall_reason;
    rand bit branch_predicted;
    rand bit [31:0] instruction;
    bit valid;
    bit ready;
    bit [63:0] timestamp;

    constraint addr_range {
        addr[63:48] == 16'h0000;
    }

    constraint size_range {
        size inside {[1:8]};
    }

    constraint burst_length {
        burst == 0;
        length == 0;
    }

    constraint data_valid {
        if(opcode == OP_LOAD) {
            data == 0;
        }
    }

    function new(string name = "cpu_transaction");
        super.new(name);
    endfunction

    function string convert2string();
        string s;
        $sformat(s, "op=%s addr=0x%0h data=0x%0h size=%0d priv=%s",
                 opcode.name(), addr, data, size, privilege.name());
        return s;
    endfunction

    function bit compare(uvm_object rhs);
        cpu_transaction rhs_tr;
        if(rhs == null) return 0;
        if(!$cast(rhs_tr, rhs)) return 0;
        return (opcode == rhs_tr.opcode) &&
               (addr == rhs_tr.addr) &&
               (data == rhs_tr.data) &&
               (size == rhs_tr.size);
    endfunction
endclass

`endif
