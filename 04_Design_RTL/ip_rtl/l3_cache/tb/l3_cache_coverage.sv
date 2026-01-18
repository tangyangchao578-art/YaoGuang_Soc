// ============================================================================
// Class: l3_cache_coverage
// Description: L3 Cache Coverage Collector
// Version: 1.0
// ============================================================================

`ifndef L3_CACHE_COVERAGE_SV
`define L3_CACHE_COVERAGE_SV

class l3_cache_coverage extends uvm_monitor;

    uvm_analysis_imp#(l3_cache_seq_item, l3_cache_coverage) analysis_export;

    // 覆盖组
    covergroup cache_cg;
        cp_addr: coverpoint addr {
            bins low    = {[0x00000000:0x0FFFFFFF]};
            bins mid    = {[0x10000000:0x7FFFFFFF]};
            bins high   = {[0x80000000:0xFFFFFFFF]};
        }
        cp_is_read: coverpoint is_read {
            bins read = {1};
            bins write = {0};
        }
        cp_len: coverpoint len {
            bins single = {0};
            bins burst4 = {3};
            bins burst8 = {7};
            bins burst16 = {15};
        }
        cp_size: coverpoint size {
            bins size8 = {3};
            bins size64 = {6};
        }
        cp_master: coverpoint master_id {
            bins masters[16] = {[0:15]};
        }
        cross cp_addr, cp_is_read;
        cross cp_len, cp_size;
    endgroup

    l3_cache_seq_item              item;

    `uvm_component_utils(l3_cache_coverage)

    function new(string name = "l3_cache_coverage", uvm_component parent = null);
        super.new(name, parent);
        analysis_export = new("analysis_export", this);
        cache_cg = new();
    endfunction

    virtual function void write(l3_cache_seq_item trans);
        item = trans;
        cache_cg.sample();
    endfunction

    virtual function real get_coverage();
        return cache_cg.get_coverage();
    endfunction

endclass

`endif
