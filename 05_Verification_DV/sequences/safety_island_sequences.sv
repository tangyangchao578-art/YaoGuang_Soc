//-----------------------------------------------------------------------------
// Safety Island Test Sequences
// YaoGuang SoC ASIL-D Safety Module Verification
// All Test Sequences for Safety Island Module
//-----------------------------------------------------------------------------
`ifndef SAFETY_ISLAND_SEQUENCES_SV
`define SAFETY_ISLAND_SEQUENCES_SV

//===============================================================================
// Base Sequence
//===============================================================================
class safety_island_base_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(safety_island_base_seq)
    
    int                         num_trans = 100;
    int                         timeout_cycles = 10000;
    
    function new(string name = "safety_island_base_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        int count = 0;
        
        for(int i = 0; i < num_trans; i++) begin
            if(count >= timeout_cycles) begin
                `uvm_warning("SEQ", "Timeout reached")
                break;
            end
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            if(!randomize(tr)) begin
                `uvm_warning("SEQ", "Randomization failed")
            end
            finish_item(tr);
            count++;
        end
    endtask
endclass

//===============================================================================
// Lockstep Sequences (SI-LOCK-001 ~ SI-LOCK-009)
//===============================================================================
class lockstep_basic_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(lockstep_basic_seq)
    
    function new(string name = "lockstep_basic_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        repeat(50) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_LOCKSTEP;
            if(!randomize(tr)) `uvm_warning("SEQ", "Randomization failed")
            finish_item(tr);
        end
    endtask
endclass

class lockstep_sync_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(lockstep_sync_seq)
    
    function new(string name = "lockstep_sync_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        repeat(100) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_LOCKSTEP;
            tr.data = 32'h00000000;
            if(!randomize(tr)) `uvm_warning("SEQ", "Randomization failed")
            finish_item(tr);
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_LOCKSTEP_COMP;
            if(!randomize(tr)) `uvm_warning("SEQ", "Randomization failed")
            finish_item(tr);
        end
    endtask
endclass

class lockstep_compare_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(lockstep_compare_seq)
    
    function new(string name = "lockstep_compare_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        for(int i = 0; i < 100; i++) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_LOCKSTEP;
            tr.data = $random();
            finish_item(tr);
            
            #10ns;
        end
    endtask
endclass

class lockstep_error_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(lockstep_error_seq)
    
    function new(string name = "lockstep_error_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        repeat(20) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_FAULT_INJECT;
            tr.data = 32'h00000001;
            finish_item(tr);
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_LOCKSTEP;
            tr.data = $random();
            finish_item(tr);
        end
    endtask
endclass

class lockstep_recovery_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(lockstep_recovery_seq)
    
    function new(string name = "lockstep_recovery_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        for(int i = 0; i < 30; i++) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_FAULT_INJECT;
            tr.data = 32'h00000001;
            finish_item(tr);
            
            #100ns;
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_FAULT_CLEAR;
            finish_item(tr);
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_LOCKSTEP;
            tr.data = $random();
            finish_item(tr);
        end
    endtask
endclass

class lockstep_timing_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(lockstep_timing_seq)
    
    function new(string name = "lockstep_timing_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        for(int i = 0; i < 1000; i++) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_LOCKSTEP;
            tr.data = i;
            finish_item(tr);
            #1ns;
        end
    endtask
endclass

class lockstep_stress_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(lockstep_stress_seq)
    
    function new(string name = "lockstep_stress_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        fork
            begin
                for(int i = 0; i < 500; i++) begin
                    tr = safety_island_transaction::type_id::create("tr");
                    start_item(tr);
                    tr.opcode = SI_OP_LOCKSTEP;
                    tr.data = $random();
                    finish_item(tr);
                end
            end
            begin
                for(int i = 0; i < 500; i++) begin
                    tr = safety_island_transaction::type_id::create("tr");
                    start_item(tr);
                    tr.opcode = SI_OP_STATUS_READ;
                    finish_item(tr);
                end
            end
        join
    endtask
endclass

class lockstep_deterministic_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(lockstep_deterministic_seq)
    
    function new(string name = "lockstep_deterministic_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        int seed = 12345;
        
        for(int i = 0; i < 100; i++) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            if(!randomize(tr) with {opcode == SI_OP_LOCKSTEP;}) begin
                `uvm_warning("SEQ", "Randomization failed")
            end
            finish_item(tr);
        end
    endtask
endclass

class lockstep_interrupt_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(lockstep_interrupt_seq)
    
    function new(string name = "lockstep_interrupt_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        for(int i = 0; i < 50; i++) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_LOCKSTEP;
            tr.data = 32'hFFFFFFFF;
            finish_item(tr);
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_NOP;
            finish_item(tr);
        end
    endtask
endclass

//===============================================================================
// ECC Sequences (SI-ECC-001 ~ SI-ECC-008)
//===============================================================================
class ecc_basic_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(ecc_basic_seq)
    
    function new(string name = "ecc_basic_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        for(int i = 0; i < 100; i++) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_ECC_WRITE;
            tr.data = $random();
            tr.addr = i * 4;
            finish_item(tr);
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_ECC_READ;
            tr.addr = i * 4;
            finish_item(tr);
        end
    endtask
endclass

class ecc_single_bit_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(ecc_single_bit_seq)
    
    function new(string name = "ecc_single_bit_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        for(int i = 0; i < 50; i++) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_ECC_WRITE;
            tr.data = 32'h00000001;
            tr.addr = i * 4;
            finish_item(tr);
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_FAULT_INJECT;
            tr.data = 32'h00000001;
            finish_item(tr);
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_ECC_READ;
            tr.addr = i * 4;
            finish_item(tr);
        end
    endtask
endclass

class ecc_double_bit_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(ecc_double_bit_seq)
    
    function new(string name = "ecc_double_bit_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        for(int i = 0; i < 50; i++) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_ECC_WRITE;
            tr.data = 32'h00000003;
            tr.addr = i * 4;
            finish_item(tr);
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_FAULT_INJECT;
            tr.data = 32'h00000003;
            finish_item(tr);
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_ECC_READ;
            tr.addr = i * 4;
            finish_item(tr);
        end
    endtask
endclass

class ecc_correction_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(ecc_correction_seq)
    
    function new(string name = "ecc_correction_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        for(int i = 0; i < 100; i++) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_ECC_WRITE;
            tr.data = $random();
            tr.addr = i * 4;
            finish_item(tr);
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_FAULT_INJECT;
            tr.data = 32'h00000001;
            finish_item(tr);
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_ECC_CORRECT;
            finish_item(tr);
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_ECC_READ;
            tr.addr = i * 4;
            finish_item(tr);
        end
    endtask
endclass

class ecc_uncorrectable_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(ecc_uncorrectable_seq)
    
    function new(string name = "ecc_uncorrectable_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        for(int i = 0; i < 20; i++) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_ECC_WRITE;
            tr.data = 32'hFFFFFFFF;
            tr.addr = i * 4;
            finish_item(tr);
            
            repeat(3) begin
                tr = safety_island_transaction::type_id::create("tr");
                start_item(tr);
                tr.opcode = SI_OP_FAULT_INJECT;
                tr.data = 32'h00000003;
                finish_item(tr);
            end
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_ECC_READ;
            tr.addr = i * 4;
            finish_item(tr);
        end
    endtask
endclass

class ecc_stress_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(ecc_stress_seq)
    
    function new(string name = "ecc_stress_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        fork
            begin
                for(int i = 0; i < 500; i++) begin
                    tr = safety_island_transaction::type_id::create("tr");
                    start_item(tr);
                    tr.opcode = SI_OP_ECC_WRITE;
                    tr.data = $random();
                    tr.addr = (i % 256) * 4;
                    finish_item(tr);
                end
            end
            begin
                for(int i = 0; i < 500; i++) begin
                    tr = safety_island_transaction::type_id::create("tr");
                    start_item(tr);
                    tr.opcode = SI_OP_ECC_READ;
                    tr.addr = (i % 256) * 4;
                    finish_item(tr);
                end
            end
        join
    endtask
endclass

class ecc_boundary_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(ecc_boundary_seq)
    
    function new(string name = "ecc_boundary_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        int addresses[] = {0, 4, 16, 64, 256, 1024, 4096, 16384, 65536};
        
        foreach(addresses[i]) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_ECC_WRITE;
            tr.data = $random();
            tr.addr = addresses[i];
            finish_item(tr);
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_ECC_READ;
            tr.addr = addresses[i];
            finish_item(tr);
        end
    endtask
endclass

class ecc_parity_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(ecc_parity_seq)
    
    function new(string name = "ecc_parity_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        for(int i = 0; i < 100; i++) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_ECC_WRITE;
            tr.data = $random();
            finish_item(tr);
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_STATUS_READ;
            finish_item(tr);
        end
    endtask
endclass

//===============================================================================
// Watchdog Sequences (SI-WDG-001 ~ SI-WDG-008)
//===============================================================================
class wdg_basic_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(wdg_basic_seq)
    
    function new(string name = "wdg_basic_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        for(int i = 0; i < 100; i++) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_WDG_KICK;
            finish_item(tr);
            #10ns;
        end
    endtask
endclass

class wdg_timeout_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(wdg_timeout_seq)
    
    function new(string name = "wdg_timeout_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        tr = safety_island_transaction::type_id::create("tr");
        start_item(tr);
        tr.opcode = SI_OP_WDG_CONFIG;
        tr.data = 32'h00000001;
        finish_item(tr);
        
        #500ns;
        
        tr = safety_island_transaction::type_id::create("tr");
        start_item(tr);
        tr.opcode = SI_OP_WDG_TIMEOUT;
        finish_item(tr);
    endtask
endclass

class wdg_kick_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(wdg_kick_seq)
    
    function new(string name = "wdg_kick_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        for(int i = 0; i < 200; i++) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_WDG_KICK;
            finish_item(tr);
            #5ns;
        end
    endtask
endclass

class wdg_config_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(wdg_config_seq)
    
    function new(string name = "wdg_config_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        for(int i = 0; i < 10; i++) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_WDG_CONFIG;
            tr.data = $random();
            finish_item(tr);
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_CONFIG_READ;
            finish_item(tr);
        end
    endtask
endclass

class wdg_reset_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(wdg_reset_seq)
    
    function new(string name = "wdg_reset_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        tr = safety_island_transaction::type_id::create("tr");
        start_item(tr);
        tr.opcode = SI_OP_WDG_CONFIG;
        tr.data = 32'h00000001;
        finish_item(tr);
        
        #100ns;
        
        for(int i = 0; i < 1000; i++) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_NOP;
            finish_item(tr);
            #1ns;
        end
        
        tr = safety_island_transaction::type_id::create("tr");
        start_item(tr);
        tr.opcode = SI_OP_RESET;
        finish_item(tr);
    endtask
endclass

class wdg_window_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(wdg_window_seq)
    
    function new(string name = "wdg_window_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        for(int i = 0; i < 50; i++) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_WDG_CONFIG;
            tr.data = 32'h00000002;
            finish_item(tr);
            
            #20ns;
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_WDG_KICK;
            finish_item(tr);
        end
    endtask
endclass

class wdg_state_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(wdg_state_seq)
    
    function new(string name = "wdg_state_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        for(int i = 0; i < 100; i++) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_STATUS_READ;
            finish_item(tr);
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_WDG_KICK;
            finish_item(tr);
        end
    endtask
endclass

class wdg_freeze_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(wdg_freeze_seq)
    
    function new(string name = "wdg_freeze_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        tr = safety_island_transaction::type_id::create("tr");
        start_item(tr);
        tr.opcode = SI_OP_WDG_CONFIG;
        tr.data = 32'h00000004;
        finish_item(tr);
        
        #100ns;
        
        tr = safety_island_transaction::type_id::create("tr");
        start_item(tr);
        tr.opcode = SI_OP_WDG_KICK;
        finish_item(tr);
        
        #50ns;
        
        tr = safety_island_transaction::type_id::create("tr");
        start_item(tr);
        tr.opcode = SI_OP_WDG_KICK;
        finish_item(tr);
    endtask
endclass

//===============================================================================
// Fault Injection Sequences (SI-FLT-001 ~ SI-FLT-005)
//===============================================================================
class fault_inject_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(fault_inject_seq)
    
    function new(string name = "fault_inject_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        for(int i = 0; i < 100; i++) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_FAULT_INJECT;
            tr.data = $random();
            finish_item(tr);
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_FAULT_STATUS;
            finish_item(tr);
        end
    endtask
endclass

class fault_reg_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(fault_reg_seq)
    
    function new(string name = "fault_reg_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        for(int i = 0; i < 50; i++) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_CONFIG_WRITE;
            tr.addr = i * 4;
            tr.data = $random();
            finish_item(tr);
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_FAULT_INJECT;
            tr.data = 32'h00000001;
            finish_item(tr);
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_CONFIG_READ;
            tr.addr = i * 4;
            finish_item(tr);
        end
    endtask
endclass

class fault_mem_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(fault_mem_seq)
    
    function new(string name = "fault_mem_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        for(int i = 0; i < 50; i++) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_ECC_WRITE;
            tr.addr = i * 4;
            tr.data = $random();
            finish_item(tr);
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_FAULT_INJECT;
            tr.data = 32'h00000001;
            finish_item(tr);
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_ECC_READ;
            tr.addr = i * 4;
            finish_item(tr);
        end
    endtask
endclass

class fault_recovery_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(fault_recovery_seq)
    
    function new(string name = "fault_recovery_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        for(int i = 0; i < 30; i++) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_FAULT_INJECT;
            tr.data = $random();
            finish_item(tr);
            
            #50ns;
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_FAULT_CLEAR;
            finish_item(tr);
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_STATUS_READ;
            finish_item(tr);
        end
    endtask
endclass

class fault_escalation_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(fault_escalation_seq)
    
    function new(string name = "fault_escalation_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        for(int i = 0; i < 10; i++) begin
            repeat(5) begin
                tr = safety_island_transaction::type_id::create("tr");
                start_item(tr);
                tr.opcode = SI_OP_FAULT_INJECT;
                tr.data = $random();
                finish_item(tr);
                #10ns;
            end
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_STATUS_READ;
            finish_item(tr);
            
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            tr.opcode = SI_OP_FAULT_CLEAR;
            finish_item(tr);
        end
    endtask
endclass

//===============================================================================
// Random and Stress Test Sequences
//===============================================================================
class safety_island_random_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(safety_island_random_seq)
    
    function new(string name = "safety_island_random_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        safety_island_opcode_t ops[] = {
            SI_OP_LOCKSTEP, SI_OP_ECC_WRITE, SI_OP_ECC_READ,
            SI_OP_WDG_KICK, SI_OP_WDG_CONFIG, SI_OP_FAULT_INJECT,
            SI_OP_FAULT_CLEAR, SI_OP_STATUS_READ, SI_OP_CONFIG_WRITE,
            SI_OP_CONFIG_READ, SI_OP_LOCKSTEP_COMP, SI_OP_ECC_CORRECT
        };
        
        for(int i = 0; i < 1000; i++) begin
            tr = safety_island_transaction::type_id::create("tr");
            start_item(tr);
            if(!randomize(tr) with {opcode inside {ops};}) begin
                `uvm_warning("SEQ", "Randomization failed")
            end
            finish_item(tr);
            #1ns;
        end
    endtask
endclass

class safety_island_stress_seq extends uvm_sequence#(safety_island_transaction);
    `uvm_object_utils(safety_island_stress_seq)
    
    function new(string name = "safety_island_stress_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        safety_island_transaction tr;
        
        fork
            begin
                for(int i = 0; i < 2000; i++) begin
                    tr = safety_island_transaction::type_id::create("tr");
                    start_item(tr);
                    tr.opcode = SI_OP_LOCKSTEP;
                    tr.data = $random();
                    finish_item(tr);
                end
            end
            begin
                for(int i = 0; i < 2000; i++) begin
                    tr = safety_island_transaction::type_id::create("tr");
                    start_item(tr);
                    tr.opcode = SI_OP_ECC_WRITE;
                    tr.data = $random();
                    tr.addr = $random();
                    finish_item(tr);
                end
            end
            begin
                for(int i = 0; i < 2000; i++) begin
                    tr = safety_island_transaction::type_id::create("tr");
                    start_item(tr);
                    tr.opcode = SI_OP_FAULT_INJECT;
                    tr.data = $random();
                    finish_item(tr);
                end
            end
        join
    endtask
endclass

`endif
