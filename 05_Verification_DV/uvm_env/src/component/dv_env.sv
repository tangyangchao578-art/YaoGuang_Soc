`ifndef DV_ENV_SVH
`define DV_ENV_SVH

class dv_env extends uvm_env;

  dv_agent  agent;
  dv_scoreboard scoreboard;
  dv_coverage coverage;

  dv_config cfg;

  `uvm_component_utils(dv_env)

  function new(string name = "dv_env", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    cfg = dv_config::get(this);

    agent = dv_agent::type_id::create("agent", this);
    agent.cfg = cfg;

    if (cfg.enable_scoreboard) begin
      scoreboard = dv_scoreboard::type_id::create("scoreboard", this);
    end

    if (cfg.enable_coverage) begin
      coverage = dv_coverage::type_id::create("coverage", this);
    end
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    agent.monitor.item_collected_port.connect(scoreboard.item_collected_export);
    agent.monitor.item_collected_port.connect(coverage.item_collected_export);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    `DV_INFO("Starting DV verification environment")

    fork
      agent.run();
      scoreboard.run();
      coverage.run();
    join_none

    phase.drop_objection(this);
  endtask

endclass

`endif
