`ifndef DV_DRIVER_SVH
`define DV_DRIVER_SVH

class dv_driver extends uvm_driver #(dv_sequence_item);
  virtual dv_if vif;

  `uvm_component_utils(dv_driver)

  function new(string name = "dv_driver", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual dv_if)::get(this, "", "vif", vif)) begin
      `uvm_fatal("NOVIF", "Virtual interface not set")
    end
  endfunction

  virtual task run_phase(uvm_phase phase);
    forever begin
      seq_item_port.get_next_item(req);
      drive_transaction(req);
      seq_item_port.item_done();
    end
  endtask

  virtual task drive_transaction(dv_sequence_item tr);
    if (tr.rw == 0) begin
      // Read transaction
      vif.apb_read(tr.addr);
    end else begin
      // Write transaction
      vif.apb_write(tr.addr, tr.data);
    end
  endtask
endclass

`endif
