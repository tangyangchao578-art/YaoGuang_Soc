`ifndef DV_COVERAGE_SVH
`define DV_COVERAGE_SVH

class dv_coverage extends uvm_component;

  uvm_analysis_imp #(axi4_transaction, dv_coverage) item_collected_export;

  covergroup axi4_txn_cg with function sample(axi4_transaction tr);
    option.per_instance = 1;

    cp_access: coverpoint tr.access {
      bins read = {axi4_transaction::READ};
      bins write = {axi4_transaction::WRITE};
    }

    cp_burst: coverpoint tr.burst {
      bins fixed = {axi4_transaction::FIXED};
      bins incr = {axi4_transaction::INCR};
      bins wrap = {axi4_transaction::WRAP};
    }

    cp_len: coverpoint tr.len {
      bins len_1 = {0};
      bins len_4 = {3};
      bins len_8 = {7};
      bins len_16 = {15};
    }

    cp_size: coverpoint tr.size {
      bins size_8 = {0};
      bins size_16 = {1};
      bins size_32 = {2};
      bins size_64 = {3};
    }

    cr_access_burst: cross cp_access, cp_burst;
  endgroup

  covergroup pmu_power_cg;
    option.per_instance = 1;

    cp_domain: coverpoint power_domain {
      bins cpu = {PD_CPU};
      bins npu = {PD_NPU};
      bins gpu = {PD_GPU};
      bins mem = {PD_MEM};
      bins all = {PD_ALL};
    }

    cp_state: coverpoint power_state {
      bins off = {POWER_OFF};
      bins on = {POWER_ON};
      bins retention = {POWER_RETENTION};
    }

    cr_domain_state: cross cp_domain, cp_state;
  endgroup

  int unsignedaxi4_cover_count = 0;
  int unsignedpmu_cover_count = 0;

  `uvm_component_utils(dv_coverage)

  function new(string name = "dv_coverage", uvm_component parent = null);
    super.new(name, parent);
    item_collected_export = new("item_collected_export", this);
    axi4_txn_cg = new();
    pmu_power_cg = new();
  endfunction

  virtual function void write(axi4_transaction tr);
    axi4_txn_cg.sample(tr);
    axi4_cover_count++;
  endfunction

  virtual function void sample_pmu(pmu_transaction tr);
    pmu_power_cg.sample();
    pmu_cover_count++;
  endfunction

  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);

    `DV_INFO($sformatf("Coverage report:"))
    `DV_INFO($sformatf("  AXI4 transactions: %0d", axi4_cover_count))
    `DV_INFO($sformatf("  PMU samples: %0d", pmu_cover_count))
    `DV_INFO($sformatf("  AXI4 coverage: %0f%%", axi4_txn_cg.get_coverage()))
    `DV_INFO($sformatf("  PMU coverage: %0f%%", pmu_power_cg.get_coverage()))
  endfunction

endclass

`endif
