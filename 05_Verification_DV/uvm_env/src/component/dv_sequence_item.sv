`ifndef DV_SEQUENCE_ITEM_SVH
`define DV_SEQUENCE_ITEM_SVH

class dv_sequence_item extends uvm_sequence_item;
  rand bit [31:0] addr;
  rand bit [31:0] data;
  rand bit rw;
  rand int delay;

  `uvm_object_utils_begin(dv_sequence_item)
    `uvm_field_int(addr, UVM_DEFAULT)
    `uvm_field_int(data, UVM_DEFAULT)
    `uvm_field_int(rw, UVM_DEFAULT)
    `uvm_field_int(delay, UVM_DEFAULT)
  `uvm_object_utils_end

  function new(string name = "dv_sequence_item");
    super.new(name);
  endfunction
endclass

`endif
