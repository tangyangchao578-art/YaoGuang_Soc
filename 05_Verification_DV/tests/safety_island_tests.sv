//-----------------------------------------------------------------------------
// Safety Island Test Package
// YaoGuang SoC ASIL-D Safety Module Verification
// All Test Cases for Safety Island Module
//-----------------------------------------------------------------------------
`ifndef SAFETY_ISLAND_TESTS_SV
`define SAFETY_ISLAND_TESTS_SV

//===============================================================================
// Base Test Class
//===============================================================================
class safety_island_base_test extends uvm_test;
    `uvm_component_utils(safety_island_base_test)
    
    safety_island_env             env;
    safety_island_env_config      cfg;
    
    function new(string name = "safety_island_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        cfg = safety_island_env_config::type_id::create("cfg");
        cfg.agent_cfg = safety_island_agent_config::type_id::create("agent_cfg");
        cfg.enable_coverage = 1;
        cfg.enable_scoreboard = 1;
        cfg.num_iterations = 1000;
        
        uvm_config_db#(safety_island_env_config)::set(this, "*", "cfg", cfg);
        
        env = safety_island_env::type_id::create("env", this);
    endfunction
    
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        uvm_top.print_topology();
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

//===============================================================================
// Double Lockstep Tests (SI-LOCK-001 ~ SI-LOCK-009)
//===============================================================================
class safety_island_lockstep_test_001 extends safety_island_base_test;
    `uvm_component_utils(safety_island_lockstep_test_001)
    
    lockstep_basic_seq seq;
    
    function new(string name = "safety_island_lockstep_test_001", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = lockstep_basic_seq::type_id::create("seq");
    endtask
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-LOCK-001: Basic Lockstep Function", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_lockstep_test_002 extends safety_island_base_test;
    `uvm_component_utils(safety_island_lockstep_test_002)
    
    lockstep_sync_seq seq;
    
    function new(string name = "safety_island_lockstep_test_002", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = lockstep_sync_seq::type_id::create("seq");
    endtask
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-LOCK-002: Lockstep Synchronization", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_lockstep_test_003 extends safety_island_base_test;
    `uvm_component_utils(safety_island_lockstep_test_003)
    
    lockstep_compare_seq seq;
    
    function new(string name = "safety_island_lockstep_test_003", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = lockstep_compare_seq::type_id::create("seq");
    endtask
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-LOCK-003: Lockstep Comparison", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_lockstep_test_004 extends safety_island_base_test;
    `uvm_component_utils(safety_island_lockstep_test_004)
    
    lockstep_error_seq seq;
    
    function new(string name = "safety_island_lockstep_test_004", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = lockstep_error_seq::type_id::create("seq");
    endtask
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-LOCK-004: Lockstep Error Detection", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_lockstep_test_005 extends safety_island_base_test;
    `uvm_component_utils(safety_island_lockstep_test_005)
    
    lockstep_recovery_seq seq;
    
    function new(string name = "safety_island_lockstep_test_005", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = lockstep_recovery_seq::type_id::create("seq");
    endtask
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-LOCK-005: Lockstep Recovery", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_lockstep_test_006 extends safety_island_base_test;
    `uvm_component_utils(safety_island_lockstep_test_006)
    
    lockstep_timing_seq seq;
    
    function new(string name = "safety_island_lockstep_test_006", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = lockstep_timing_seq::type_id::create("seq");
    endtask
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-LOCK-006: Lockstep Timing", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_lockstep_test_007 extends safety_island_base_test;
    `uvm_component_utils(safety_island_lockstep_test_007)
    
    lockstep_stress_seq seq;
    
    function new(string name = "safety_island_lockstep_test_007", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = lockstep_stress_seq::type_id::create("seq");
    endtask
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-LOCK-007: Lockstep Stress Test", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_lockstep_test_008 extends safety_island_base_test;
    `uvm_component_utils(safety_island_lockstep_test_008)
    
    lockstep_deterministic_seq seq;
    
    function new(string name = "safety_island_lockstep_test_008", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = lockstep_deterministic_seq::type_id::create("seq");
    endtask
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-LOCK-008: Lockstep Deterministic Execution", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_lockstep_test_009 extends safety_island_base_test;
    `uvm_component_utils(safety_island_lockstep_test_009)
    
    lockstep_interrupt_seq seq;
    
    function new(string name = "safety_island_lockstep_test_009", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = lockstep_interrupt_seq::type_id::create("seq");
    endtask
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-LOCK-009: Lockstep Interrupt Latency", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

//===============================================================================
// ECC Tests (SI-ECC-001 ~ SI-ECC-008)
//===============================================================================
class safety_island_ecc_test_001 extends safety_island_base_test;
    `uvm_component_utils(safety_island_ecc_test_001)
    
    ecc_basic_seq seq;
    
    function new(string name = "safety_island_ecc_test_001", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = ecc_basic_seq::type_id::create("seq");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-ECC-001: Basic ECC Function", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_ecc_test_002 extends safety_island_base_test;
    `uvm_component_utils(safety_island_ecc_test_002)
    
    ecc_single_bit_seq seq;
    
    function new(string name = "safety_island_ecc_test_002", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = ecc_single_bit_seq::type_id::create("seq");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-ECC-002: Single Bit Error Detection", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_ecc_test_003 extends safety_island_base_test;
    `uvm_component_utils(safety_island_ecc_test_003)
    
    ecc_double_bit_seq seq;
    
    function new(string name = "safety_island_ecc_test_003", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = ecc_double_bit_seq::type_id::create("seq");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-ECC-003: Double Bit Error Detection", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_ecc_test_004 extends safety_island_base_test;
    `uvm_component_utils(safety_island_ecc_test_004)
    
    ecc_correction_seq seq;
    
    function new(string name = "safety_island_ecc_test_004", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = ecc_correction_seq::type_id::create("seq");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-ECC-004: Single Bit Error Correction", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_ecc_test_005 extends safety_island_base_test;
    `uvm_component_utils(safety_island_ecc_test_005)
    
    ecc_uncorrectable_seq seq;
    
    function new(string name = "safety_island_ecc_test_005", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = ecc_uncorrectable_seq::type_id::create("seq");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-ECC-005: Uncorrectable Error Handling", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_ecc_test_006 extends safety_island_base_test;
    `uvm_component_utils(safety_island_ecc_test_006)
    
    ecc_stress_seq seq;
    
    function new(string name = "safety_island_ecc_test_006", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = ecc_stress_seq::type_id::create("seq");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-ECC-006: ECC Stress Test", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_ecc_test_007 extends safety_island_base_test;
    `uvm_component_utils(safety_island_ecc_test_007)
    
    ecc_boundary_seq seq;
    
    function new(string name = "safety_island_ecc_test_007", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = ecc_boundary_seq::type_id::create("seq");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-ECC-007: Boundary Test", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_ecc_test_008 extends safety_island_base_test;
    `uvm_component_utils(safety_island_ecc_test_008)
    
    ecc_parity_seq seq;
    
    function new(string name = "safety_island_ecc_test_008", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = ecc_parity_seq::type_id::create("seq");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-ECC-008: ECC Parity Test", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

//===============================================================================
// Watchdog Tests (SI-WDG-001 ~ SI-WDG-008)
//===============================================================================
class safety_island_wdg_test_001 extends safety_island_base_test;
    `uvm_component_utils(safety_island_wdg_test_001)
    
    wdg_basic_seq seq;
    
    function new(string name = "safety_island_wdg_test_001", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = wdg_basic_seq::type_id::create("seq");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-WDG-001: Basic Watchdog Function", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_wdg_test_002 extends safety_island_base_test;
    `uvm_component_utils(safety_island_wdg_test_002)
    
    wdg_timeout_seq seq;
    
    function new(string name = "safety_island_wdg_test_002", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = wdg_timeout_seq::type_id::create("seq");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-WDG-002: Watchdog Timeout", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_wdg_test_003 extends safety_island_base_test;
    `uvm_component_utils(safety_island_wdg_test_003)
    
    wdg_kick_seq seq;
    
    function new(string name = "safety_island_wdg_test_003", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = wdg_kick_seq::type_id::create("seq");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-WDG-003: Watchdog Kick", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_wdg_test_004 extends safety_island_base_test;
    `uvm_component_utils(safety_island_wdg_test_004)
    
    wdg_config_seq seq;
    
    function new(string name = "safety_island_wdg_test_004", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = wdg_config_seq::type_id::create("seq");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-WDG-004: Watchdog Configuration", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_wdg_test_005 extends safety_island_base_test;
    `uvm_component_utils(safety_island_wdg_test_005)
    
    wdg_reset_seq seq;
    
    function new(string name = "safety_island_wdg_test_005", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = wdg_reset_seq::type_id::create("seq");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-WDG-005: Watchdog Reset Generation", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_wdg_test_006 extends safety_island_base_test;
    `uvm_component_utils(safety_island_wdg_test_006)
    
    wdg_window_seq seq;
    
    function new(string name = "safety_island_wdg_test_006", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = wdg_window_seq::type_id::create("seq");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-WDG-006: Watchdog Window", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_wdg_test_007 extends safety_island_base_test;
    `uvm_component_utils(safety_island_wdg_test_007)
    
    wdg_state_seq seq;
    
    function new(string name = "safety_island_wdg_test_007", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = wdg_state_seq::type_id::create("seq");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-WDG-007: Watchdog State Machine", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_wdg_test_008 extends safety_island_base_test;
    `uvm_component_utils(safety_island_wdg_test_008)
    
    wdg_freeze_seq seq;
    
    function new(string name = "safety_island_wdg_test_008", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = wdg_freeze_seq::type_id::create("seq");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-WDG-008: Watchdog Freeze", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

//===============================================================================
// Fault Injection Tests (SI-FLT-001 ~ SI-FLT-005)
//===============================================================================
class safety_island_fault_test_001 extends safety_island_base_test;
    `uvm_component_utils(safety_island_fault_test_001)
    
    fault_inject_seq seq;
    
    function new(string name = "safety_island_fault_test_001", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = fault_inject_seq::type_id::create("seq");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-FLT-001: Basic Fault Injection", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_fault_test_002 extends safety_island_base_test;
    `uvm_component_utils(safety_island_fault_test_002)
    
    fault_reg_seq seq;
    
    function new(string name = "safety_island_fault_test_002", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = fault_reg_seq::type_id::create("seq");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-FLT-002: Register Fault Injection", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_fault_test_003 extends safety_island_base_test;
    `uvm_component_utils(safety_island_fault_test_003)
    
    fault_mem_seq seq;
    
    function new(string name = "safety_island_fault_test_003", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = fault_mem_seq::type_id::create("seq");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-FLT-003: Memory Fault Injection", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_fault_test_004 extends safety_island_base_test;
    `uvm_component_utils(safety_island_fault_test_004)
    
    fault_recovery_seq seq;
    
    function new(string name = "safety_island_fault_test_004", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = fault_recovery_seq::type_id::create("seq");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-FLT-004: Fault Recovery", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_fault_test_005 extends safety_island_base_test;
    `uvm_component_utils(safety_island_fault_test_005)
    
    fault_escalation_seq seq;
    
    function new(string name = "safety_island_fault_test_005", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = fault_escalation_seq::type_id::create("seq");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting SI-FLT-005: Fault Escalation", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

//===============================================================================
// Additional Coverage Tests
//===============================================================================
class safety_island_random_test extends safety_island_base_test;
    `uvm_component_utils(safety_island_random_test)
    
    safety_island_random_seq seq;
    
    function new(string name = "safety_island_random_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = safety_island_random_seq::type_id::create("seq");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting Safety Island Random Test", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

class safety_island_stress_test extends safety_island_base_test;
    `uvm_component_utils(safety_island_stress_test)
    
    safety_island_stress_seq seq;
    
    function new(string name = "safety_island_stress_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq = safety_island_stress_seq::type_id::create("seq");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Starting Safety Island Stress Test", UVM_LOW)
        seq.start(env.agent.sequencer);
        #1us;
        phase.drop_objection(this);
    endtask
endclass

`endif
