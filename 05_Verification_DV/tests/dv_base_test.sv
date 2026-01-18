`ifndef DV_TEST_SVH
`define DV_TEST_SVH

class dv_base_test extends uvm_test;

  dv_env env;

  `uvm_component_utils(dv_base_test)

  function new(string name = "dv_base_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    env = dv_env::type_id::create("env", this);

    `DV_INFO("DV base test built")
  endfunction

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);

    `DV_INFO("Starting DV base test")
  endtask

  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);

    `DV_INFO("DV base test completed")
  endfunction

endclass

class dv_sanity_test extends dv_base_test;

  dv_reg_sequence reg_seq;

  `uvm_component_utils(dv_sanity_test)

  function new(string name = "dv_sanity_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    `DV_INFO("Running sanity test")

    reg_seq = dv_reg_sequence::type_id::create("reg_seq");
    reg_seq.start(env.agent.sequencer);

    #1000;

    phase.drop_objection(this);
  endtask

endclass

`endif
