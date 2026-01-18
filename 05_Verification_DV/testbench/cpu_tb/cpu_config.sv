//-----------------------------------------------------------------------------
// File: cpu_config.sv
// Description: CPU Subsystem verification configuration
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef CPU_CONFIG_SV
`define CPU_CONFIG_SV

class cpu_config extends uvm_object;
    `uvm_object_utils(cpu_config)

    // Core configuration
    int num_cores = 4;
    int has_l1_cache = 1;
    int has_l2_cache = 1;
    int l1_cache_size = 32; // KB
    int l2_cache_size = 256; // KB
    int l1_line_size = 64; // bytes
    int l2_line_size = 64; // bytes
    int l1_ways = 4;
    int l2_ways = 8;

    // GIC configuration
    int num_irq = 256;
    int num_sgi = 16;
    int num_ppi = 16;
    int gic_version = 2; // GICv2

    // MMU configuration
    int asid_bits = 16;
    int va_bits = 48;
    int pa_bits = 40;

    // Virtualization
    int has_virtualization = 1;
    int vmid_bits = 8;

    // Simulation options
    bit enable_debug = 1;
    bit enable_coverage = 1;
    int max_sim_cycles = 1000000;
    int heartbeat_interval = 10000;

    // Error injection
    bit inject_cache_error = 0;
    bit inject_tlb_error = 0;
    bit inject_memory_error = 0;
    real error_rate = 0.001;

    // Performance monitoring
    bit enable_perf_mon = 1;
    int perf_counters = 6;

    // Reset configuration
    bit enable_por_reset = 1;
    bit enable_warm_reset = 1;
    int reset_assert_cycles = 10;

    // Address map
    bit [63:0] dram_base = 64'h0000_0000_0000_0000;
    bit [63:0] dram_size = 64'h0000_0001_0000_0000;
    bit [63:0] peripheral_base = 64'h4000_0000_0000_0000;
    bit [63:0] peripheral_size = 64'h0000_0000_1000_0000;

    // Function coverage toggle
    bit cov_cache_enable = 1;
    bit cov_mmu_enable = 1;
    bit cov_gic_enable = 1;
    bit cov_pipeline_enable = 1;

    function new(string name = "cpu_config");
        super.new(name);
    endfunction

    function string get_config_summary();
        string summary = "";
        $sformat(summary, "CPU Config: %0d cores, L1:%0dKB(%0d-way), L2:%0dKB(%0d-way)",
                 num_cores, l1_cache_size, l1_ways, l2_cache_size, l2_ways);
        return summary;
    endfunction
endclass

`endif
