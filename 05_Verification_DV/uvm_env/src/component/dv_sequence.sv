`ifndef DV_SEQUENCE_SVH
`define DV_SEQUENCE_SVH

class dv_sequence extends uvm_sequence #(dv_sequence_item);
  `uvm_object_utils(dv_sequence)

  int num_transactions = 10;

  function new(string name = "dv_sequence");
    super.new(name);
  endfunction

  virtual task body();
    for (int i = 0; i < num_transactions; i++) begin
      dv_sequence_item item = dv_sequence_item::type_id::create("item");
      start_item(item);
      item.randomize();
      item.addr = 'h1000_0000 + i * 4;
      item.rw = i % 2;
      item.data = 'hDEADBEEF;
      finish_item(item);
    end
  endtask
endclass

class dv_reg_sequence extends uvm_sequence #(dv_sequence_item);
  `uvm_object_utils(dv_reg_sequence)

  function new(string name = "dv_reg_sequence");
    super.new(name);
  endfunction

  virtual task body();
    // Read register test
    for (int i = 0; i < 10; i++) begin
      dv_sequence_item item = dv_sequence_item::type_id::create("reg_read");
      start_item(item);
      item.randomize();
      item.addr = 'h4000_0000 + i * 4;
      item.rw = 0; // Read
      finish_item(item);
    end

    // Write register test
    for (int i = 0; i < 10; i++) begin
      dv_sequence_item item = dv_sequence_item::type_id::create("reg_write");
      start_item(item);
      item.randomize();
      item.addr = 'h4000_0000 + i * 4;
      item.rw = 1; // Write
      item.data = i;
      finish_item(item);
    end
  endtask
endclass

`endif
