class safety_lockstep_test extends dv_base_test;

  `uvm_component_utils(safety_lockstep_test)

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    `DV_INFO("Testing Safety Island lockstep")

    // Test basic lockstep operation
    begin
      lockstep_basic_seq seq = lockstep_basic_seq::type_id::create("lockstep_seq");
      seq.start(env.agent.sequencer);
    end

    // Test error detection
    begin
      lockstep_error_seq seq = lockstep_error_seq::type_id::create("lockstep_error_seq");
      seq.inject_single_bit_error(1);
      seq.start(env.agent.sequencer);
    end

    // Test response time
    begin
      lockstep_timing_seq seq = lockstep_timing_seq::type_id::create("lockstep_timing_seq");
      seq.start(env.agent.sequencer);
    end

    phase.drop_objection(this);
  endtask

endclass

class safety_ecc_test extends dv_base_test;

  `uvm_component_utils(safety_ecc_test)

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    `DV_INFO("Testing Safety Island ECC")

    // Test single-bit error correction
    begin
      ecc_single_bit_seq seq = ecc_single_bit_seq::type_id::create("ecc_single_seq");
      seq.inject_error(1, 0);
      seq.start(env.agent.sequencer);
    end

    // Test double-bit error detection
    begin
      ecc_double_bit_seq seq = ecc_double_bit_seq::type_id::create("ecc_double_seq");
      seq.inject_error(2, 0);
      seq.start(env.agent.sequencer);
    end

    // Test ECC interrupt
    begin
      ecc_interrupt_seq seq = ecc_interrupt_seq::type_id::create("ecc_int_seq");
      seq.start(env.agent.sequencer);
    end

    phase.drop_objection(this);
  endtask

endclass

class safety_watchdog_test extends dv_base_test;

  `uvm_component_utils(safety_watchdog_test)

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    `DV_INFO("Testing Safety Island watchdog")

    // Test internal watchdog
    begin
      watchdog_internal_seq seq = watchdog_internal_seq::type_id::create("wdg_int_seq");
      seq.timeout_ms = 100;
      seq.feed = 0;
      seq.start(env.agent.sequencer);
    end

    // Test window watchdog
    begin
      watchdog_window_seq seq = watchdog_window_seq::type_id::create("wdg_window_seq");
      seq.start(env.agent.sequencer);
    end

    // Test external watchdog
    begin
      watchdog_external_seq seq = watchdog_external_seq::type_id::create("wdg_ext_seq");
      seq.start(env.agent.sequencer);
    end

    phase.drop_objection(this);
  endtask

endclass

class safety_fault_injection_test extends dv_base_test;

  `uvm_component_utils(safety_fault_injection_test)

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    `DV_INFO("Testing Safety Island fault injection")

    // Inject various faults and verify detection
    for (int i = 0; i < 100; i++) begin
      fault_injection_seq seq = fault_injection_seq::type_id::create("fault_seq");
      seq.randomize();
      seq.start(env.agent.sequencer);
      #100;
    end

    phase.drop_objection(this);
  endtask

endclass
