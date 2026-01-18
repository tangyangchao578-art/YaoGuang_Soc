//-----------------------------------------------------------------------------
// Safety Island Package File
// YaoGuang SoC ASIL-D Safety Module Verification
// Top-level package that includes all verification components
//-----------------------------------------------------------------------------
`ifndef SAFETY_ISLAND_PKG_SV
`define SAFETY_ISLAND_PKG_SV

package safety_island_pkg;
    `include "uvm_macros.svh"
    
    // Import UVM package
    import uvm_pkg::*;
    
    // Include all verification components
    `include "safety_island_transaction.sv"
    `include "safety_island_if.sv"
    `include "safety_island_driver.sv"
    `include "safety_island_monitor.sv"
    `include "safety_island_sequencer.sv"
    `include "safety_island_agent.sv"
    `include "safety_island_scoreboard.sv"
    `include "safety_island_coverage.sv"
    `include "safety_island_env.sv"
    `include "safety_island_sequences.sv"
    `include "safety_island_tests.sv"
    
endpackage

`endif
