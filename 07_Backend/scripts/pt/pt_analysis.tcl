#!/usr/bin/env tclsh
#===============================================================================
# YaoGuang SoC PrimeTime Timing Analysis Main Script
#===============================================================================
# Version: V1.0
# Date: 2026-01-18
# Author: YaoGuang Backend Team
# Description: Main PrimeTime analysis script for YaoGuang SoC timing signoff
#===============================================================================

#===============================================================================
# Section 1: Library and Environment Setup
#===============================================================================

# Library paths configuration
set_app_var search_path "$search_path \
    /lib/saed5nm/tt_0p9v_25c \
    /lib/saed5nm/ss_0p81v_m40c \
    /lib/saed5nm/ff_0p99v_125c \
    /lib/io_cells \
    /lib/memory_libs"

# Target library settings
set_app_var target_library "saed5nm_tt_0p9v_25c.db"

# Link library - includes all possible libraries
set_app_var link_library "* \
    saed5nm_tt_0p9v_25c.db \
    saed5nm_ss_0p81v_m40c.db \
    saed5nm_ff_0p99v_125c.db \
    io_cell_tt.db \
    sram_2kb_tt.db"

# Set timing library type
set_app_var timing_library ""

# Enable verbose output
set_app_var verbose true
set_app_var report_debug true

#===============================================================================
# Section 2: Design Database Loading
#===============================================================================

puts "\n=========================================="
puts "YaoGuang SoC PrimeTime Timing Analysis"
puts "==========================================\n"

puts "[INFO] Loading design database..."

# Read synthesized netlist
if {![file exists "../netlist/yaoguang_soc_netlist.v"]} {
    puts "ERROR: Netlist file not found!"
    exit 1
}

read_verilog ../netlist/yaoguang_soc_netlist.v
current_design yaoguang_soc_top

# Link the design
if {[link] == false} {
    puts "ERROR: Design linking failed!"
    exit 1
}

puts "[OK] Design loaded and linked successfully"

#===============================================================================
# Section 3: SDC Constraints Loading
#===============================================================================

puts "\n[INFO] Loading SDC constraints..."

if {![file exists "../sdc/yaoguang_soc_sdc.out.sdc"]} {
    puts "WARNING: SDC file not found, using default constraints"
} else {
    read_sdc ../sdc/yaoguang_soc_sdc.out.sdc
    puts "[OK] SDC constraints loaded"
}

#===============================================================================
# Section 4: Parasitic Extraction Data
#===============================================================================

puts "\n[INFO] Loading parasitic data..."

if {![file exists "../spef/yaoguang_soc.spef"]} {
    puts "WARNING: SPEF file not found, using ideal parasitics"
} else {
    read_parasitics -spef ../spef/yaoguang_soc.spef
    puts "[OK] Parasitic data loaded"
}

#===============================================================================
# Section 5: Multi-Corner Multi-Mode Setup
#===============================================================================

puts "\n[INFO] Setting up multi-corner analysis..."

# Define analysis modes
set analysis_modes {
    func_tt {setup_corner tt_0p9v_25c hold_corner tt_0p9v_25c}
    func_ss  {setup_corner ss_0p81v_m40c hold_corner ss_0p81v_m40c}
    func_ff  {setup_corner ff_0p99v_125c hold_corner ff_0p99v_125c}
    wcs      {setup_corner ss_0p81v_m40c hold_corner ss_0p81v_m40c}
    bcs      {setup_corner ff_0p99v_125c hold_corner ff_0p99v_125c}
}

foreach mode [array names analysis_modes] {
    puts "  - $mode: [lindex $analysis_modes($mode) 0], [lindex $analysis_modes($mode) 1]"
}

#===============================================================================
# Section 6: Timing Update
#===============================================================================

puts "\n[INFO] Updating timing data..."

update_timing -verbose

puts "[OK] Timing data updated"

#===============================================================================
# Section 7: Clock Definition Verification
#===============================================================================

puts "\n=========================================="
puts "Clock Domain Summary"
puts "==========================================\n"

# Clock information
set clocks {
    clk_core {frequency 2000MHz period 0.5ns source sysclk_pll}
    clk_npu  {frequency 2000MHz period 0.5ns source npu_pll}
    clk_sys  {frequency 500MHz  period 2.0ns source apb_clk}
    clk_mem  {frequency 800MHz  period 1.25ns source ddr_clk}
}

foreach clk [array names clocks] {
    puts "  Clock: $clk"
    puts "    Period: [dict get $clocks($clk) period]"
    puts "    Frequency: [dict get $clocks($clk) frequency]"
}

report_clock -summary

#===============================================================================
# Section 8: Timing Analysis
#===============================================================================

puts "\n=========================================="
puts "Timing Analysis Results"
puts "==========================================\n"

# Setup Analysis (WCS - Worst Case Slow)
puts "\n--- Setup Analysis (WCS Corner) ---\n"
set_analysis_mode -setup ss_0p81v_m40c
set_analysis_mode -hold ss_0p81v_m40c

set setup_slack [report_timing -delay_type max -max_paths 50 -slack_lesser_than 0 -significant_digits 3]
puts "Setup Slack Summary: $setup_slack"

# Hold Analysis (BCS - Best Case Fast)
puts "\n--- Hold Analysis (BCS Corner) ---\n"
set_analysis_mode -setup ff_0p99v_125c
set_analysis_mode -hold ff_0p99v_125c

set hold_slack [report_timing -delay_type min -max_paths 50 -slack_lesser_than 0 -significant_digits 3]
puts "Hold Slack Summary: $hold_slack"

#===============================================================================
# Section 9: Comprehensive Timing Reports
#===============================================================================

puts "\n=========================================="
puts "Generating Timing Reports"
puts "==========================================\n"

# Setup report
report_timing -delay_type max \
    -max_paths 100 \
    -sort_by slack \
    -slack_lesser_than 0 \
    -significant_digits 3 \
    -input_pins \
    -report_path_type full \
    -output ../reports/timing_setup_wcs.rpt

# Hold report
report_timing -delay_type min \
    -max_paths 100 \
    -slack_lesser_than 0 \
    -significant_digits 3 \
    -report_path_type full \
    -output ../reports/timing_hold_bcs.rpt

# Recovery/Removal report
report_timing -recovery -max_paths 20 -output ../reports/timing_recovery.rpt
report_timing -removal -max_paths 20 -output ../reports/timing_removal.rpt

# Clock reports
report_clock -summary -output ../reports/clock_summary.rpt
report_clock_timing -type waveforms -output ../reports/clock_waveforms.rpt
report_clock_tree -summary -output ../reports/clock_tree_summary.rpt

puts "[OK] All timing reports generated"

#===============================================================================
# Section 10: Timing Check
#===============================================================================

puts "\n=========================================="
puts "Timing Check Results"
puts "==========================================\n"

check_timing -verbose

#===============================================================================
# Section 11: Power Analysis
#===============================================================================

puts "\n=========================================="
puts "Power Analysis"
puts "==========================================\n"

report_power -hierarchy -significant_digits 3 -output ../reports/power_report.rpt

#===============================================================================
# Section 12: Signoff Summary
#===============================================================================

puts "\n=========================================="
puts "Timing Signoff Summary"
puts "==========================================\n"

# Collect timing metrics
set setup_violations [get_timing_paths -delay_type max -slack_lesser_than 0]
set hold_violations [get_timing_paths -delay_type min -slack_lesser_than 0]

set setup_violation_count [llength $setup_violations]
set hold_violation_count [llength $hold_violations]

puts "Setup Violations (WCS): $setup_violation_count"
puts "Hold Violations (BCS):  $hold_violation_count"

if {$setup_violation_count == 0 && $hold_violation_count == 0} {
    puts "\n*** TIMING SIGNOFF PASSED ***\n"
} else {
    puts "\n*** TIMING SIGNOFF FAILED - REVISIONS REQUIRED ***\n"
}

# Save database
save_session ../sessions/pt_session.session

puts "\n=========================================="
puts "PrimeTime Analysis Complete"
puts "==========================================\n"

exit 0
