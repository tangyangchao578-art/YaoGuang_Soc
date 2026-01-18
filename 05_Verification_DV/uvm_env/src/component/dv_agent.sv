`ifndef DV_AGENT_SVH
`define DV_AGENT_SVH

class dv_agent extends uvm_agent;
  dv_config cfg;
  dv_driver driver;
  dv_monitor monitor;
  dv_sequencer sequencer;

  `uvm_component_utils(dv_agent)

  function new(string name = "dv_agent", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    cfg = dv_config::get(this);

    driver = dv_driver::type_id::create("driver", this);
    monitor = dv_monitor::type_id::create("monitor", this);
    sequencer = dv_sequencer::type_id::create("sequencer", this);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    driver.seq_item_port.connect(sequencer.seq_item_export);
  endfunction

  virtual task run_phase(uvm_phase phase);
    `DV_INFO("DV agent starting")
  endtask
endclass

`endif
