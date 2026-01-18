`ifndef AXI4_VIP_SVH
`define AXI4_VIP_SVH

class axi4_config extends uvm_object;
  rand int addr_width = 32;
  rand int data_width = 64;
  rand int id_width = 8;
  rand int awuser_width = 0;
  rand int aruser_width = 0;
  rand int wuser_width = 0;
  rand int ruser_width = 0;
  rand int buser_width = 0;
  rand bit has_awuser = 0;
  rand bit has_aruser = 0;
  rand bit has_wuser = 0;
  rand bit has_ruser = 0;
  rand bit has_buser = 0;

  `uvm_object_utils_begin(axi4_config)
    `uvm_field_int(addr_width, UVM_DEFAULT)
    `uvm_field_int(data_width, UVM_DEFAULT)
    `uvm_field_int(id_width, UVM_DEFAULT)
  `uvm_object_utils_end

  function new(string name = "axi4_config");
    super.new(name);
  endfunction
endclass

class axi4_transaction extends uvm_sequence_item;
  typedef enum {READ, WRITE} access_t;
  typedef enum {FIXED, INCR, WRAP} burst_t;

  rand access_t access;
  rand burst_t burst;
  rand bit [31:0] addr;
  rand int len;
  rand int size;
  rand bit [3:0] cache;
  rand bit [5:0] prot;
  rand bit [3:0] qos;
  rand bit [3:0] region;
  rand bit [7:0] id;
  rand bit [7:0] user;

  rand bit [63:0] data[];
  rand bit [7:0] wstrb[];

  bit [7:0] resp;
  int delay;

  constraint valid_addr {
    addr % (1 << size) == 0;
  }

  constraint valid_len {
    len inside {[1:16]};
  }

  constraint valid_size {
    size inside {[0:6]};
    2 ** size <= 64;
  }

  constraint valid_data {
    data.size() == len + 1;
    wstrb.size() == len + 1;
  }

  `uvm_object_utils_begin(axi4_transaction)
    `uvm_field_enum(access_t, access, UVM_DEFAULT)
    `uvm_field_enum(burst_t, burst, UVM_DEFAULT)
    `uvm_field_int(addr, UVM_DEFAULT)
    `uvm_field_int(len, UVM_DEFAULT)
    `uvm_field_int(size, UVM_DEFAULT)
    `uvm_field_int(cache, UVM_DEFAULT)
    `uvm_field_int(prot, UVM_DEFAULT)
    `uvm_field_int(id, UVM_DEFAULT)
    `uvm_field_array_int(data, UVM_DEFAULT)
    `uvm_field_array_int(wstrb, UVM_DEFAULT)
    `uvm_field_int(resp, UVM_DEFAULT)
    `uvm_field_int(delay, UVM_DEFAULT)
  `uvm_object_utils_end

  function new(string name = "axi4_transaction");
    super.new(name);
  endfunction
endclass

class axi4_driver extends uvm_driver #(axi4_transaction);
  axi4_config cfg;
  virtual axi4_if vif;

  `uvm_component_utils(axi4_driver)

  function new(string name = "axi4_driver", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual task run_phase(uvm_phase phase);
    forever begin
      seq_item_port.get_next_item(req);
      drive_transaction(req);
      seq_item_port.item_done();
    end
  endtask

  virtual task drive_transaction(axi4_transaction tr);
    vif.awvalid <= 0;
    vif.arvalid <= 0;
    vif.wvalid <= 0;
    vif.bready <= 1;
    vif.rready <= 1;

    if (tr.access == WRITE) begin
      drive_aw(tr);
      drive_w(tr);
      wait (vif.bvalid);
      tr.resp = vif.bresp;
    end else begin
      drive_ar(tr);
      wait (vif.rvalid);
      while (vif.rlast == 0) begin
        tr.data.push_back(vif.rdata);
        tr.resp = vif.rresp;
        wait (vif.rvalid);
      end
      tr.data.push_back(vif.rdata);
    end
  endtask

  virtual task drive_aw(axi4_transaction tr);
    vif.awvalid <= 1;
    vif.awaddr <= tr.addr;
    vif.awid <= tr.id;
    vif.awlen <= tr.len;
    vif.awsize <= tr.size;
    vif.awburst <= tr.burst;
    vif.awcache <= tr.cache;
    vif.awprot <= tr.prot;
    vif.awqos <= tr.qos;
    wait (vif.awready);
    @(posedge vif.clk);
    vif.awvalid <= 0;
  endtask

  virtual task drive_ar(axi4_transaction tr);
    vif.arvalid <= 1;
    vif.araddr <= tr.addr;
    vif.arid <= tr.id;
    vif.arlen <= tr.len;
    vif.arsize <= tr.size;
    vif.arburst <= tr.burst;
    vif.arcache <= tr.cache;
    vif.arprot <= tr.prot;
    vif.arqos <= tr.qos;
    wait (vif.arready);
    @(posedge vif.clk);
    vif.arvalid <= 0;
  endtask

  virtual task drive_w(axi4_transaction tr);
    for (int i = 0; i <= tr.len; i++) begin
      vif.wvalid <= 1;
      vif.wdata <= tr.data[i];
      vif.wstrb <= tr.wstrb[i];
      vif.wlast <= (i == tr.len);
      wait (vif.wready);
      @(posedge vif.clk);
    end
    vif.wvalid <= 0;
  endtask
endclass

class axi4_monitor extends uvm_monitor;
  axi4_config cfg;
  virtual axi4_if vif;

  uvm_analysis_port #(axi4_transaction) item_collected_port;

  `uvm_component_utils(axi4_monitor)

  function new(string name = "axi4_monitor", uvm_component parent = null);
    super.new(name, parent);
    item_collected_port = new("item_collected_port", this);
  endfunction

  virtual task run_phase(uvm_phase phase);
    forever begin
      @(posedge vif.clk);
      if (vif.awvalid && vif.awready) begin
        axi4_transaction tr = new();
        tr.access = axi4_transaction::WRITE;
        tr.addr = vif.awaddr;
        tr.id = vif.awid;
        tr.len = vif.awlen;
        tr.size = vif.awsize;
        tr.burst = burst_t'(vif.awburst);
        item_collected_port.write(tr);
      end
      if (vif.arvalid && vif.arready) begin
        axi4_transaction tr = new();
        tr.access = axi4_transaction::READ;
        tr.addr = vif.araddr;
        tr.id = vif.arid;
        tr.len = vif.arlen;
        tr.size = vif.arsize;
        tr.burst = burst_t'(vif.arburst);
        item_collected_port.write(tr);
      end
    end
  endtask
endclass

class axi4_sequencer extends uvm_sequencer #(axi4_transaction);
  `uvm_component_utils(axi4_sequencer)

  function new(string name = "axi4_sequencer", uvm_component parent = null);
    super.new(name, parent);
  endfunction
endclass

class axi4_agent extends uvm_agent;
  axi4_config cfg;
  axi4_driver driver;
  axi4_monitor monitor;
  axi4_sequencer sequencer;

  `uvm_component_utils(axi4_agent)

  function new(string name = "axi4_agent", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    driver = axi4_driver::type_id::create("driver", this);
    monitor = axi4_monitor::type_id::create("monitor", this);
    sequencer = axi4_sequencer::type_id::create("sequencer", this);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    driver.seq_item_port.connect(sequencer.seq_item_export);
  endtask
endclass

`endif
