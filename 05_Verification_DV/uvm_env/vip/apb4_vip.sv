`ifndef APB4_VIP_SVH
`define APB4_VIP_SVH

class apb_config extends uvm_object;
  rand int addr_width = 32;
  rand int data_width = 32;
  rand int prot_width = 3;

  `uvm_object_utils_begin(apb_config)
    `uvm_field_int(addr_width, UVM_DEFAULT)
    `uvm_field_int(data_width, UVM_DEFAULT)
  `uvm_object_utils_end

  function new(string name = "apb_config");
    super.new(name);
  endfunction
endclass

class apb_transaction extends uvm_sequence_item;
  typedef enum {READ, WRITE} access_t;

  rand access_t access;
  rand bit [31:0] addr;
  rand bit [31:0] data;
  rand bit [3:0] strb;
  rand bit [2:0] prot;

  bit [31:0] read_data;
  bit [1:0] resp;

  constraint valid_strb {
    strb inside {4'b0001, 4'b0011, 4'b1111};
  }

  `uvm_object_utils_begin(apb_transaction)
    `uvm_field_enum(access_t, access, UVM_DEFAULT)
    `uvm_field_int(addr, UVM_DEFAULT)
    `uvm_field_int(data, UVM_DEFAULT)
    `uvm_field_int(strb, UVM_DEFAULT)
    `uvm_field_int(prot, UVM_DEFAULT)
    `uvm_field_int(read_data, UVM_DEFAULT)
    `uvm_field_int(resp, UVM_DEFAULT)
  `uvm_object_utils_end

  function new(string name = "apb_transaction");
    super.new(name);
  endfunction
endclass

class apb_driver extends uvm_driver #(apb_transaction);
  apb_config cfg;
  virtual apb_if vif;

  `uvm_component_utils(apb_driver)

  function new(string name = "apb_driver", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual task run_phase(uvm_phase phase);
    forever begin
      seq_item_port.get_next_item(req);
      drive_transaction(req);
      seq_item_port.item_done();
    end
  endtask

  virtual task drive_transaction(apb_transaction tr);
    vif.psel <= 0;
    vif.penable <= 0;
    vif.pwrite <= (tr.access == apb_transaction::WRITE);
    vif.paddr <= tr.addr;
    `ifdef APB4
    vif.pstrb <= tr.strb;
    vif.pprot <= tr.prot;
    `endif

    @(posedge vif.pclk);
    vif.psel <= 1;
    vif.pwdata <= tr.data;

    wait (vif.pready);
    tr.read_data = vif.prdata;
    tr.resp = vif.preset;

    @(posedge vif.pclk);
    vif.psel <= 0;
    vif.penable <= 0;
  endtask
endclass

class apb_monitor extends uvm_monitor;
  apb_config cfg;
  virtual apb_if vif;

  uvm_analysis_port #(apb_transaction) item_collected_port;

  `uvm_component_utils(apb_monitor)

  function new(string name = "apb_monitor", uvm_component parent = null);
    super.new(name, parent);
    item_collected_port = new("item_collected_port", this);
  endfunction

  virtual task run_phase(uvm_phase phase);
    forever begin
      @(posedge vif.pclk);
      if (vif.psel && vif.penable && !vif.pwrite) begin
        wait (vif.pready);
        apb_transaction tr = new();
        tr.access = apb_transaction::READ;
        tr.addr = vif.paddr;
        tr.read_data = vif.prdata;
        tr.resp = vif.preset;
        item_collected_port.write(tr);
      end
      if (vif.psel && vif.penable && vif.pwrite) begin
        wait (vif.pready);
        apb_transaction tr = new();
        tr.access = apb_transaction::WRITE;
        tr.addr = vif.paddr;
        tr.data = vif.pwdata;
        tr.resp = vif.preset;
        item_collected_port.write(tr);
      end
    end
  endtask
endclass

class apb_sequencer extends uvm_sequencer #(apb_transaction);
  `uvm_component_utils(apb_sequencer)

  function new(string name = "apb_sequencer", uvm_component parent = null);
    super.new(name, parent);
  endfunction
endclass

class apb_agent extends uvm_agent;
  apb_config cfg;
  apb_driver driver;
  apb_monitor monitor;
  apb_sequencer sequencer;

  `uvm_component_utils(apb_agent)

  function new(string name = "apb_agent", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    driver = apb_driver::type_id::create("driver", this);
    monitor = apb_monitor::type_id::create("monitor", this);
    sequencer = apb_sequencer::type_id::create("sequencer", this);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    driver.seq_item_port.connect(sequencer.seq_item_export);
  endtask
endclass

`endif
