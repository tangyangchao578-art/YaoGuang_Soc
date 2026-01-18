//-----------------------------------------------------------------------------
// File: l3_cache_config.sv
// Description: L3 Cache verification configuration
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef L3_CACHE_CONFIG_SV
`define L3_CACHE_CONFIG_SV

class l3_cache_config extends uvm_object;
    `uvm_object_utils(l3_cache_config)

    int l3_cache_size = 2048;
    int l3_line_size = 64;
    int l3_ways = 16;
    int num_banks = 4;
    int bank_size = 512;
    int lru_bits = 4;
    int tag_depth = 1024;
    int data_depth = 2048;

    int max_outstanding = 16;
    int read_latency = 4;
    int write_latency = 4;

    bit enable_snoop = 1;
    bit enable_writeback = 1;
    bit enable_allocate = 1;

    bit inject_error = 0;
    real error_rate = 0.0001;

    bit enable_coverage = 1;
    bit enable_debug = 0;

    bit [63:0] base_address = 64'h0000_0000_0000_0000;
    bit [63:0] size_address = 64'h0000_0002_0000_0000;

    function new(string name = "l3_cache_config");
        super.new(name);
    endfunction

    function string get_config_summary();
        string summary = "";
        $sformat(summary, "L3 Config: %0dKB(%0d-way, %0d banks)", l3_cache_size, l3_ways, num_banks);
        return summary;
    endfunction
endclass

`endif
