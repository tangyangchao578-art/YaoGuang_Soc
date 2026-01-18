#!/usr/bin/env tclsh
#===============================================================================
# YaoGuang SoC Timing Report Generation Script
#===============================================================================
# Version: V1.0
# Date: 2026-01-18
# Author: YaoGuang Backend Team
# Description: Comprehensive timing report generation for all analysis types
#===============================================================================

#===============================================================================
# Section 1: Initialization and Setup
#===============================================================================

puts "\n=========================================="
puts "YaoGuang SoC Timing Report Generator"
puts "==========================================\n"

# Set report directory
set report_dir "../reports"
if {![file exists $report_dir]} {
    file mkdir $report_dir
    puts "[INFO] Created report directory: $report_dir"
}

# Set significant digits for reports
set_app_var report_significant_digits 3

#===============================================================================
# Section 2: Setup Analysis Reports
#===============================================================================

puts "\n[INFO] Generating Setup Timing Reports..."

#------------------------------------------------------------------------------
# 2.1 Maximum Delay Analysis (Setup Time)
#------------------------------------------------------------------------------

puts "\n--- Generating Setup (Max Delay) Report ---\n"

report_timing -delay_type max \
    -max_paths 100 \
    -sort_by slack \
    -slack_lesser_than 0 \
    -significant_digits 3 \
    -input_pins \
    -report_path_type full \
    -output $report_dir/timing_setup_max_paths.rpt

# Setup analysis with detailed path information
report_timing -delay_type max \
    -max_paths 50 \
    -slack_lesser_than 0.5 \
    -significant_digits 3 \
    -transition_time \
    -capacitance \
    -net \
    -output $report_dir/timing_setup_detailed.rpt

# Setup analysis grouped by clock domain
report_timing -delay_type max \
    -max_paths 100 \
    -group [get_clocks clk_core] \
    -output $report_dir/timing_setup_clk_core.rpt

report_timing -delay_type max \
    -max_paths 100 \
    -group [get_clocks clk_npu] \
    -output $report_dir/timing_setup_clk_npu.rpt

report_timing -delay_type max \
    -max_paths 100 \
    -group [get_clocks clk_sys] \
    -output $report_dir/timing_setup_clk_sys.rpt

report_timing -delay_type max \
    -max_paths 100 \
    -group [get_clocks clk_mem] \
    -output $report_dir/timing_setup_clk_mem.rpt

puts "[OK] Setup reports generated"

#===============================================================================
# Section 3: Hold Analysis Reports
#===============================================================================

puts "\n[INFO] Generating Hold Timing Reports..."

#------------------------------------------------------------------------------
# 3.1 Minimum Delay Analysis (Hold Time)
#------------------------------------------------------------------------------

report_timing -delay_type min \
    -max_paths 100 \
    -slack_lesser_than 0 \
    -significant_digits 3 \
    -input_pins \
    -report_path_type full \
    -output $report_dir/timing_hold_min_paths.rpt

# Hold analysis with detailed path information
report_timing -delay_type min \
    -max_paths 50 \
    -slack_lesser_than 0.1 \
    -significant_digits 3 \
    -transition_time \
    -capacitance \
    -net \
    -output $report_dir/timing_hold_detailed.rpt

# Hold analysis grouped by clock domain
report_timing -delay_type min \
    -max_paths 100 \
    -group [get_clocks clk_core] \
    -output $report_dir/timing_hold_clk_core.rpt

report_timing -delay_type min \
    -max_paths 100 \
    -group [get_clocks clk_npu] \
    -output $report_dir/timing_hold_clk_npu.rpt

report_timing -delay_type min \
    -max_paths 100 \
    -group [get_clocks clk_sys] \
    -output $report_dir/timing_hold_clk_sys.rpt

report_timing -delay_type min \
    -max_paths 100 \
    -group [get_clocks clk_mem] \
    -output $report_dir/timing_hold_clk_mem.rpt

puts "[OK] Hold reports generated"

#===============================================================================
# Section 4: Recovery and Removal Analysis
#===============================================================================

puts "\n[INFO] Generating Recovery/Removal Reports..."

# Recovery time analysis
report_timing -recovery \
    -max_paths 50 \
    -significant_digits 3 \
    -report_path_type full \
    -output $report_dir/timing_recovery.rpt

# Removal time analysis
report_timing -removal \
    -max_paths 50 \
    -significant_digits 3 \
    -report_path_type full \
    -output $report_dir/timing_removal.rpt

puts "[OK] Recovery/Removal reports generated"

#===============================================================================
# Section 5: Clock Analysis Reports
#===============================================================================

puts "\n[INFO] Generating Clock Analysis Reports..."

# Clock summary
report_clock -summary -output $report_dir/clock_summary.rpt

# Clock waveform details
report_clock_timing -type waveforms -output $report_dir/clock_waveforms.rpt

# Clock tree summary
report_clock_tree -summary -output $report_dir/clock_tree_summary.rpt

# Clock skew report
report_clock_timing -type skew -output $report_dir/clock_skew.rpt

# Clock latency report
report_clock_timing -type latency -output $report_dir/clock_latency.rpt

# Clock uncertainty report
report_clock_timing -type uncertainty -output $report_dir/clock_uncertainty.rpt

puts "[OK] Clock reports generated"

#===============================================================================
# Section 6: Voltage Domain Analysis
#===============================================================================

puts "\n[INFO] Generating Voltage Domain Reports..."

# Core domain timing
report_timing -max_paths 50 \
    -to [get_pins */vdda_core_regulator*] \
    -output $report_dir/timing_core_domain.rpt

# Memory domain timing
report_timing -max_paths 50 \
    -to [get_pins */vdda_mem_regulator*] \
    -output $report_dir/timing_mem_domain.rpt

# IO domain timing
report_timing -max_paths 50 \
    -to [get_pins */vdda_io_regulator*] \
    -output $report_dir/timing_io_domain.rpt

puts "[OK] Voltage domain reports generated"

#===============================================================================
# Section 7: Module-Level Timing Reports
#===============================================================================

puts "\n[INFO] Generating Module-Level Reports..."

# CPU Core module
report_timing -max_paths 50 \
    -to [get_pins */cpu_core_inst/*] \
    -from [get_pins */cpu_core_inst/*] \
    -output $report_dir/timing_cpu_core.rpt

# NPU module
report_timing -max_paths 50 \
    -to [get_pins */npu_inst/*] \
    -from [get_pins */npu_inst/*] \
    -output $report_dir/timing_npu.rpt

# System bus module
report_timing -max_paths 50 \
    -to [get_pins */axi_bus_inst/*] \
    -from [get_pins */axi_bus_inst/*] \
    -output $report_dir/timing_bus.rpt

# DDR controller
report_timing -max_paths 50 \
    -to [get_pins */ddr_ctrl_inst/*] \
    -from [get_pins */ddr_ctrl_inst/*] \
    -output $report_dir/timing_ddr_ctrl.rpt

# Peripheral controllers
report_timing -max_paths 50 \
    -to [get_pins */periph_inst/*] \
    -output $report_dir/timing_peripherals.rpt

puts "[OK] Module-level reports generated"

#===============================================================================
# Section 8: Interface Timing Reports
#===============================================================================

puts "\n[INFO] Generating Interface Timing Reports..."

# Clock domain crossing (CDC) analysis
report_timing -delay_type max \
    -max_paths 100 \
    -through [get_cells -filter "is_sequential==false"] \
    -output $report_dir/timing_cdc_paths.rpt

# Async clock interface
report_timing -max_paths 20 \
    -through [get_cells -filter "is_sequential==false"] \
    -from [get_clocks clk_sys] \
    -to [get_clocks clk_mem] \
    -output $report_dir/timing_async_interface.rpt

puts "[OK] Interface reports generated"

#===============================================================================
# Section 9: Multi-Corner Timing Reports
#===============================================================================

puts "\n[INFO] Generating Multi-Corner Reports..."

# Typical corner
set_analysis_mode -setup tt_0p9v_25c
set_analysis_mode -hold tt_0p9v_25c
report_timing -output $report_dir/timing_tt_corner.rpt

# Slow-Slow corner (WCS)
set_analysis_mode -setup ss_0p81v_m40c
set_analysis_mode -hold ss_0p81v_m40c
report_timing -delay_type max -max_paths 50 -output $report_dir/timing_ss_setup.rpt
report_timing -delay_type min -max_paths 50 -output $report_dir/timing_ss_hold.rpt

# Fast-Fast corner (BCS)
set_analysis_mode -setup ff_0p99v_125c
set_analysis_mode -hold ff_0p99v_125c
report_timing -delay_type max -max_paths 50 -output $report_dir/timing_ff_setup.rpt
report_timing -delay_type min -max_paths 50 -output $report_dir/timing_ff_hold.rpt

# Return to typical corner
set_analysis_mode -setup tt_0p9v_25c
set_analysis_mode -hold tt_0p9v_25c

puts "[OK] Multi-corner reports generated"

#===============================================================================
# Section 10: Timing Violation Summary
#===============================================================================

puts "\n=========================================="
puts "Timing Violation Summary"
puts "==========================================\n"

# Collect all violations
set setup_violations [get_timing_paths -delay_type max -slack_lesser_than 0]
set hold_violations [get_timing_paths -delay_type min -slack_lesser_than 0]
set recovery_violations [get_timing_paths -recovery -slack_lesser_than 0]
set removal_violations [get_timing_paths -removal -slack_lesser_than 0]

set setup_violation_count [llength $setup_violations]
set hold_violation_count [llength $hold_violations]
set recovery_violation_count [llength $recovery_violations]
set removal_violation_count [llength $removal_violations]

# Create violation summary report
set summary_report "YaoGuang SoC Timing Violation Summary\n"
append summary_report "=====================================\n\n"
append summary_report "Setup Violations (Max Delay): $setup_violation_count\n"
append summary_report "Hold Violations (Min Delay):  $hold_violation_count\n"
append summary_report "Recovery Violations:          $recovery_violation_count\n"
append summary_report "Removal Violations:           $removal_violation_count\n\n"

# Worst setup violations
if {$setup_violation_count > 0} {
    append summary_report "Worst Setup Violations:\n"
    append summary_report "------------------------\n"
    set worst_setup [lrange [lsort -real -index 1 [get_timing_paths -delay_type max -slack_lesser_than 0]] 0 9]
    foreach path $worst_setup {
        append summary_report "  [get_object_name $path]: Slack=[get_property $path slack] ps\n"
    }
}

# Worst hold violations
if {$hold_violation_count > 0} {
    append summary_report "\nWorst Hold Violations:\n"
    append summary_report "----------------------\n"
    set worst_hold [lrange [lsort -real -index 1 [get_timing_paths -delay_type min -slack_lesser_than 0]] 0 9]
    foreach path $worst_hold {
        append summary_report "  [get_object_name $path]: Slack=[get_property $path slack] ps\n"
    }
}

# Write summary report
set summary_file [open $report_dir/timing_violation_summary.rpt w]
puts $summary_file $summary_report
close $summary_file

puts $summary_report

#===============================================================================
# Section 11: QOR (Quality of Results) Report
#===============================================================================

puts "\n=========================================="
puts "Quality of Results Summary"
puts "==========================================\n"

report_qor -output $report_dir/qor_summary.rpt

#===============================================================================
# Section 12: Final Summary
#===============================================================================

puts "\n=========================================="
puts "Timing Report Generation Complete"
puts "==========================================\n"

puts "Report directory: $report_dir"
puts "Total reports generated: [llength [glob -directory $report_dir *.rpt]]"

if {$setup_violation_count == 0 && $hold_violation_count == 0} {
    puts "\n*** ALL TIMING CHECKS PASSED ***\n"
} else {
    puts "\n*** TIMING VIOLATIONS DETECTED - SEE REPORTS ***\n"
    puts "Setup violations: $setup_violation_count"
    puts "Hold violations: $hold_violation_count"
}

exit 0
