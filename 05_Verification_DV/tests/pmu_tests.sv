class pmu_test extends dv_base_test;

  `uvm_component_utils(pmu_test)

  function new(string name = "pmu_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    `DV_INFO("Starting PMU basic test")

    begin
      pmu_reg_sequence seq = pmu_reg_sequence::type_id::create("pmu_reg_seq");
      seq.start(env.agent.sequencer);
    end

    #1000;

    phase.drop_objection(this);
  endtask

endclass

class pmu_power_on_test extends pmu_test;

  `uvm_component_utils(pmu_power_on_test)

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    `DV_INFO("Testing PMU power-on sequence")

    // Test power domain power-on
    pmu_power_on_seq seq = pmu_power_on_seq::type_id::create("pmu_power_on_seq");
    seq.domain = PD_CPU;
    seq.start(env.agent.sequencer);

    // Verify power status
    check_power_status(PD_CPU, POWER_ON);

    `DV_INFO("PMU power-on test completed")

    phase.drop_objection(this);
  endtask

  virtual function void check_power_status(int domain, bit expected);
    pmu_status_reg_t status;
    read_power_status(domain, status);
    `DV_CHECK(status.pwron == expected, "Power status mismatch")
  endfunction

endclass

class pmu_dvfs_test extends pmu_test;

  `uvm_component_utils(pmu_dvfs_test)

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    `DV_INFO("Testing PMU DVFS")

    // Test DVFS for CPU
    for (int i = 0; i < 16; i++) begin
      dvfs_sequence seq = dvfs_sequence::type_id::create("dvfs_seq");
      seq.target = CPU;
      seq.level = i;
      seq.start(env.agent.sequencer);
      #100;
    end

    `DV_INFO("PMU DVFS test completed")

    phase.drop_objection(this);
  endtask

endclass

class pmu_low_power_test extends pmu_test;

  `uvm_component_utils(pmu_low_power_test)

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    `DV_INFO("Testing PMU low power modes")

    // Test Idle mode
    enter_low_power_mode(IDLE);
    #500;
    exit_low_power_mode(IDLE);

    // Test Standby mode
    enter_low_power_mode(STANDBY);
    #1000;
    exit_low_power_mode(STANDBY);

    // Test Sleep mode
    enter_low_power_mode(SLEEP);
    #2000;
    exit_low_power_mode(SLEEP);

    // Test Deep Sleep mode
    enter_low_power_mode(DEEP_SLEEP);
    #5000;
    exit_low_power_mode(DEEP_SLEEP);

    `DV_INFO("PMU low power test completed")

    phase.drop_objection(this);
  endtask

endclass

class pmu_protection_test extends pmu_test;

  `uvm_component_utils(pmu_protection_test)

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    `DV_INFO("Testing PMU protection mechanisms")

    // Test over-voltage protection
    inject_fault(OVER_VOLTAGE);
    wait_for_protection_response();

    // Test over-current protection
    inject_fault(OVER_CURRENT);
    wait_for_protection_response();

    // Test over-temperature protection
    inject_fault(OVER_TEMPERATURE);
    wait_for_protection_response();

    // Test watchdog timeout
    inject_fault(WATCHDOG_TIMEOUT);
    wait_for_protection_response();

    `DV_INFO("PMU protection test completed")

    phase.drop_objection(this);
  endtask

endclass
