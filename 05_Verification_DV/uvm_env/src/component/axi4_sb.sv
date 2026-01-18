`ifndef AXI4_SCOREBARD_SVH
`define AXI4_SCOREBARD_SVH

class axi4_scoreboard extends uvm_scoreboard;
  axi4_transaction req_fifo[$];
  axi4_transaction rsp_fifo[$];

  int passed = 0;
  int failed = 0;

  uvm_analysis_imp #(axi4_transaction, axi4_scoreboard) item_collected_export;

  `uvm_component_utils(axi4_scoreboard)

  function new(string name = "axi4_scoreboard", uvm_component parent = null);
    super.new(name, parent);
    item_collected_export = new("item_collected_export", this);
  endfunction

  virtual function void write(axi4_transaction tr);
    if (tr.access == axi4_transaction::READ) begin
      req_fifo.push_back(tr);
    end else begin
      rsp_fifo.push_back(tr);
    end
    compare_transactions();
  endfunction

  virtual function void compare_transactions();
    while (req_fifo.size() > 0 && rsp_fifo.size() > 0) begin
      axi4_transaction req = req_fifo.pop_front();
      axi4_transaction rsp = rsp_fifo.pop_front();

      if (req.id == rsp.id && req.addr == rsp.addr) begin
        `DV_INFO("Transaction matched")
        passed++;
      end else begin
        `DV_ERROR("Transaction mismatch")
        failed++;
      end
    end
  endfunction

  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `DV_INFO($sformatf("Scoreboard report: passed=%0d, failed=%0d", passed, failed))
  endfunction
endclass

`endif
