//-----------------------------------------------------------------------------
// Safety Island Transaction
// YaoGuang SoC ASIL-D Safety Module Verification
//-----------------------------------------------------------------------------
`ifndef SAFETY_ISLAND_TRANSACTION_SV
`define SAFETY_ISLAND_TRANSACTION_SV

typedef enum bit[7:0] {
    SI_OP_NOP           = 8'h00,
    SI_OP_LOCKSTEP      = 8'h01,
    SI_OP_ECC_WRITE     = 8'h02,
    SI_OP_ECC_READ      = 8'h03,
    SI_OP_WDG_KICK      = 8'h04,
    SI_OP_WDG_CONFIG    = 8'h05,
    SI_OP_FAULT_INJECT  = 8'h06,
    SI_OP_FAULT_CLEAR   = 8'h07,
    SI_OP_STATUS_READ   = 8'h08,
    SI_OP_CONFIG_WRITE  = 8'h09,
    SI_OP_CONFIG_READ   = 8'h0A,
    SI_OP_LOCKSTEP_COMP = 8'h0B,
    SI_OP_ECC_CORRECT   = 8'h0C,
    SI_OP_WDG_TIMEOUT   = 8'h0D,
    SI_OP_FAULT_STATUS  = 8'h0E,
    SI_OP_RESET         = 8'h0F
} safety_island_opcode_t;

class safety_island_transaction extends uvm_sequence_item;
    `uvm_object_utils(safety_island_transaction)
    
    rand safety_island_opcode_t  opcode;
    rand bit[31:0]               data;
    rand bit[31:0]               addr;
    rand bit[7:0]                id;
    bit[31:0]                    resp;
    bit                          error;
    bit[1:0]                     lockstep_result;
    bit[5:0]                     ecc_status;
    bit                          wdg_status;
    bit[31:0]                    timestamp;
    
    constraint op_cons {
        opcode dist {
            SI_OP_NOP[:]5,
            SI_OP_LOCKSTEP[:]10,
            SI_OP_ECC_WRITE[:]10,
            SI_OP_ECC_READ[:]10,
            SI_OP_WDG_KICK[:]8,
            SI_OP_WDG_CONFIG[:]5,
            SI_OP_FAULT_INJECT[:]15,
            SI_OP_FAULT_CLEAR[:]10,
            SI_OP_STATUS_READ[:]5,
            SI_OP_CONFIG_WRITE[:]5,
            SI_OP_CONFIG_READ[:]5,
            SI_OP_LOCKSTEP_COMP[:]8,
            SI_OP_ECC_CORRECT[:]5,
            SI_OP_WDG_TIMEOUT[:]3,
            SI_OP_FAULT_STATUS[:]3,
            SI_OP_RESET[:]2
        };
    }
    
    function new(string name = "safety_island_transaction");
        super.new(name);
    endfunction
    
    virtual function string convert2string();
        return $sformatf("opcode=0x%0h addr=0x%0h data=0x%0h id=0x%0h", opcode, addr, data, id);
    endfunction
    
    virtual function void do_copy(uvm_object rhs);
        safety_island_transaction rhs_;
        super.do_copy(rhs);
        $cast(rhs_, rhs);
        opcode = rhs_.opcode;
        data = rhs_.data;
        addr = rhs_.addr;
        id = rhs_.id;
        resp = rhs_.resp;
        error = rhs_.error;
    endfunction
    
    virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        safety_island_transaction rhs_;
        do_compare = super.do_compare(rhs, comparer);
        $cast(rhs_, rhs);
        do_compare &= (opcode == rhs_.opcode);
        do_compare &= (addr == rhs_.addr);
        do_compare &= (data == rhs_.data);
    endfunction
endclass

`endif
