//-----------------------------------------------------------------------------
// Safety Island Coverage Model
// YaoGuang SoC ASIL-D Safety Module Verification
// Coverage Collection for 95% Code Coverage and 100% Functional Coverage
//-----------------------------------------------------------------------------
`ifndef SAFETY_ISLAND_COVERAGE_SV
`define SAFETY_ISLAND_COVERAGE_SV

covergroup safety_island_opcode_cg;
    opcode_cp: coverpoint tr.opcode {
        bins NOP           = {SI_OP_NOP};
        bins LOCKSTEP      = {SI_OP_LOCKSTEP};
        bins ECC_WRITE     = {SI_OP_ECC_WRITE};
        bins ECC_READ      = {SI_OP_ECC_READ};
        bins WDG_KICK      = {SI_OP_WDG_KICK};
        bins WDG_CONFIG    = {SI_OP_WDG_CONFIG};
        bins FAULT_INJECT  = {SI_OP_FAULT_INJECT};
        bins FAULT_CLEAR   = {SI_OP_FAULT_CLEAR};
        bins STATUS_READ   = {SI_OP_STATUS_READ};
        bins CONFIG_WRITE  = {SI_OP_CONFIG_WRITE};
        bins CONFIG_READ   = {SI_OP_CONFIG_READ};
        bins LOCKSTEP_COMP = {SI_OP_LOCKSTEP_COMP};
        bins ECC_CORRECT   = {SI_OP_ECC_CORRECT};
        bins WDG_TIMEOUT   = {SI_OP_WDG_TIMEOUT};
        bins FAULT_STATUS  = {SI_OP_FAULT_STATUS};
        bins RESET         = {SI_OP_RESET};
    }
endgroup

covergroup safety_island_data_cg;
    data_cp: coverpoint tr.data {
        bins ZERO          = {32'h00000000};
        bins ONES          = {32'hFFFFFFFF};
        bins RANDOM        = default;
    }
endgroup

covergroup safety_island_addr_cg;
    addr_cp: coverpoint tr.addr {
        bins ADDR_0        = {0};
        bins ADDR_4        = {4};
        bins ADDR_16       = {16};
        bins ADDR_64       = {64};
        bins ADDR_256      = {256};
        bins ADDR_1K       = {1024};
        bins ADDR_4K       = {4096};
        bins ADDR_RANDOM   = default;
    }
endgroup

covergroup safety_island_lockstep_cg;
    lockstep_mode: coverpoint tr.lockstep_result {
        bins MATCH         = {2'b00};
        bins MISMATCH      = {2'b01};
        bins ERROR         = {2'b10};
    }
    
    lockstep_cross: cross lockstep_mode, opcode_cg;
endgroup

covergroup safety_island_ecc_cg;
    ecc_status_cp: coverpoint tr.ecc_status {
        bins NO_ERROR      = {6'b000000};
        bins SINGLE_BIT    = {6'b000001};
        bins DOUBLE_BIT    = {6'b000011};
        bins UNCORRECTABLE = {6'b000111};
        bins CORRECTED     = {6'b000010};
    }
    
    ecc_cross: cross ecc_status_cp, opcode_cg;
endgroup

covergroup safety_island_wdg_cg;
    wdg_status_cp: coverpoint tr.wdg_status {
        bins ACTIVE         = {1'b1};
        bins INACTIVE       = {1'b0};
        bins TIMEOUT        = {1'b1};
    }
    
    wdg_cross: cross wdg_status_cp, opcode_cg;
endgroup

covergroup safety_island_fault_cg;
    fault_type: coverpoint tr.data[7:0] {
        bins REG_FAULT      = {[0:15]};
        bins MEM_FAULT      = {[16:31]};
        bins LOGIC_FAULT    = {[32:63]};
        bins TIMING_FAULT   = {[64:127]};
    }
    
    fault_cross: cross fault_type, opcode_cg;
endgroup

class safety_island_coverage extends uvm_component;
    `uvm_component_utils(safety_island_coverage)
    
    uvm_analysis_imp#(safety_island_transaction, safety_island_coverage) analysis_export;
    
    safety_island_transaction tr;
    
    safety_island_opcode_cg       opcode_cg;
    safety_island_data_cg         data_cg;
    safety_island_addr_cg         addr_cg;
    safety_island_lockstep_cg     lockstep_cg;
    safety_island_ecc_cg          ecc_cg;
    safety_island_wdg_cg          wdg_cg;
    safety_island_fault_cg        fault_cg;
    
    int                           total_transactions = 0;
    int                           lockstep_trans = 0;
    int                           ecc_trans = 0;
    int                           wdg_trans = 0;
    int                           fault_trans = 0;
    
    function new(string name = "safety_island_coverage", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        analysis_export = new("analysis_export", this);
        
        opcode_cg = new();
        data_cg = new();
        addr_cg = new();
        lockstep_cg = new();
        ecc_cg = new();
        wdg_cg = new();
        fault_cg = new();
    endfunction
    
    virtual function void write(safety_island_transaction t);
        tr = t;
        sample_coverage();
        update_stats();
    endfunction
    
    virtual protected function void sample_coverage();
        opcode_cg.sample();
        data_cg.sample();
        addr_cg.sample();
        
        case(tr.opcode)
            SI_OP_LOCKSTEP, SI_OP_LOCKSTEP_COMP: begin
                lockstep_cg.sample();
                lockstep_trans++;
            end
            SI_OP_ECC_WRITE, SI_OP_ECC_READ, SI_OP_ECC_CORRECT: begin
                ecc_cg.sample();
                ecc_trans++;
            end
            SI_OP_WDG_KICK, SI_OP_WDG_CONFIG, SI_OP_WDG_TIMEOUT: begin
                wdg_cg.sample();
                wdg_trans++;
            end
            SI_OP_FAULT_INJECT, SI_OP_FAULT_CLEAR, SI_OP_FAULT_STATUS: begin
                fault_cg.sample();
                fault_trans++;
            end
        endcase
        
        total_transactions++;
    endfunction
    
    virtual protected function void update_stats();
    endfunction
    
    virtual function real get_opcode_coverage();
        return opcode_cg.get_coverage();
    endfunction
    
    virtual function real get_data_coverage();
        return data_cg.get_coverage();
    endfunction
    
    virtual function real get_addr_coverage();
        return addr_cg.get_coverage();
    endfunction
    
    virtual function real get_lockstep_coverage();
        return lockstep_cg.get_coverage();
    endfunction
    
    virtual function real get_ecc_coverage();
        return ecc_cg.get_coverage();
    endfunction
    
    virtual function real get_wdg_coverage();
        return wdg_cg.get_coverage();
    endfunction
    
    virtual function real get_fault_coverage();
        return fault_cg.get_coverage();
    endfunction
    
    virtual function real get_overall_coverage();
        real total = 0.0;
        real count = 0.0;
        
        total += get_opcode_coverage();
        count += 100;
        total += get_data_coverage();
        count += 100;
        total += get_addr_coverage();
        count += 100;
        total += get_lockstep_coverage();
        count += 100;
        total += get_ecc_coverage();
        count += 100;
        total += get_wdg_coverage();
        count += 100;
        total += get_fault_coverage();
        count += 100;
        
        return total / count * 100;
    endfunction
    
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        `uvm_info("COV", $sformatf("=== Safety Island Coverage Report ==="), UVM_LOW)
        `uvm_info("COV", $sformatf("Opcode Coverage:    %3.1f%%", get_opcode_coverage()), UVM_LOW)
        `uvm_info("COV", $sformatf("Data Coverage:      %3.1f%%", get_data_coverage()), UVM_LOW)
        `uvm_info("COV", $sformatf("Addr Coverage:      %3.1f%%", get_addr_coverage()), UVM_LOW)
        `uvm_info("COV", $sformatf("Lockstep Coverage:  %3.1f%%", get_lockstep_coverage()), UVM_LOW)
        `uvm_info("COV", $sformatf("ECC Coverage:       %3.1f%%", get_ecc_coverage()), UVM_LOW)
        `uvm_info("COV", $sformatf("WDG Coverage:       %3.1f%%", get_wdg_coverage()), UVM_LOW)
        `uvm_info("COV", $sformatf("Fault Coverage:     %3.1f%%", get_fault_coverage()), UVM_LOW)
        `uvm_info("COV", $sformatf("Overall Coverage:   %3.1f%%", get_overall_coverage()), UVM_LOW)
        `uvm_info("COV", $sformatf("Total Transactions: %0d", total_transactions), UVM_LOW)
        `uvm_info("COV", $sformatf("Lockstep Trans:     %0d", lockstep_trans), UVM_LOW)
        `uvm_info("COV", $sformatf("ECC Trans:          %0d", ecc_trans), UVM_LOW)
        `uvm_info("COV", $sformatf("WDG Trans:          %0d", wdg_trans), UVM_LOW)
        `uvm_info("COV", $sformatf("Fault Trans:        %0d", fault_trans), UVM_LOW)
    endfunction
endclass

`endif
