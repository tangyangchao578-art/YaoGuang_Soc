`ifndef DV_MONITOR_SVH
`define DV_MONITOR_SVH

class dv_monitor extends uvm_monitor;
  virtual dv_if vif;

  uvm_analysis_port #(dv_sequence_item) item_collected_port;

  `uvm_component_utils(dv_monitor)

  function new(string name = "dv_monitor", uvm_component parent = null);
    super.new(name, parent);
    item_collected_port = new("item_collected_port", this);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual dv_if)::get(this, "", "vif", vif)) begin
      `uvm_fatal("NOVIF", "Virtual interface not set")
    end
  endfunction

  virtual task run_phase(uvm_phase phase);
    forever begin
      @(posedge vif.pclk);
      if (vif.psel && vif.penable && !vif.pwrite) begin
        wait (vif.pready);
        dv_sequence_item item = dv_sequence_item::type_id::create("mon_item");
        item.addr = vif.paddr;
        item.rw = 0;
        item.data = vif.prdata;
        item_collected_port.write(item);
      end
    end
  endtask
endclass

`endif
