#!/usr/bin/env tclsh
#===============================================================================
# YaoGuang SoC Timing Closure Script
#===============================================================================
# Version: V1.0
# Date: 2026-01-18
# Author: YaoGuang Backend Team
# Description: Timing closure analysis and optimization for YaoGuang SoC
#===============================================================================

#===============================================================================
# Section 1: Initialization
#===============================================================================

puts "\n=========================================="
puts "YaoGuang SoC Timing Closure Analysis"
puts "==========================================\n"

# Set report directory
set report_dir "../reports"
set session_dir "../sessions"

if {![file exists $report_dir]} {
    file mkdir $report_dir
}

if {![file exists $session_dir]} {
    file mkdir $session_dir
}

#===============================================================================
# Section 2: Timing Violation Collection
#===============================================================================

puts "\n=========================================="
puts "Timing Violation Analysis"
puts "==========================================\n"

# Set to WCS corner for setup analysis
set_analysis_mode -setup ss_0p81v_m40c
set_analysis_mode -hold ss_0p81v_m40c

# Collect Setup violations
puts "\n[INFO] Collecting Setup violations..."
set setup_violations [get_timing_paths -delay_type max -slack_lesser_than 0]
set setup_violation_count [llength $setup_violations]
puts "  Found $setup_violation_count Setup violations"

# Collect Hold violations
puts "\n[INFO] Collecting Hold violations..."
set hold_violations [get_timing_paths -delay_type min -slack_lesser_than 0]
set hold_violation_count [llength $hold_violations]
puts "  Found $hold_violation_count Hold violations"

# Collect Recovery violations
puts "\n[INFO] Collecting Recovery violations..."
set recovery_violations [get_timing_paths -recovery -slack_lesser_than 0]
set recovery_violation_count [llength $recovery_violations]
puts "  Found $recovery_violation_count Recovery violations"

# Collect Removal violations
puts "\n[INFO] Collecting Removal violations..."
set removal_violations [get_timing_paths -removal -slack_lesser_than 0]
set removal_violation_count [llength $removal_violations]
puts "  Found $removal_violation_count Removal violations"

#===============================================================================
# Section 3: Violation Summary
#===============================================================================

puts "\n=========================================="
puts "Violation Summary"
puts "==========================================\n"

puts "Setup Violations:    $setup_violation_count"
puts "Hold Violations:     $hold_violation_count"
puts "Recovery Violations: $recovery_violation_count"
puts "Removal Violations:  $removal_violation_count"

# Create detailed violation summary
set violation_summary "Timing Violation Summary Report\n"
append violation_summary "================================\n\n"
append violation_summary "Analysis Corner: ss_0p81v_m40c (WCS)\n\n"
append violation_summary "Violation Counts:\n"
append violation_summary "  Setup:    $setup_violation_count\n"
append violation_summary "  Hold:     $hold_violation_count\n"
append violation_summary "  Recovery: $recovery_violation_count\n"
append violation_summary "  Removal:  $removal_violation_count\n\n"

# Save violation summary
set violation_file [open $report_dir/violation_summary.rpt w]
puts $violation_file $violation_summary
close $violation_file

#===============================================================================
# Section 4: Critical Path Analysis
#===============================================================================

puts "\n=========================================="
puts "Critical Path Analysis"
puts "==========================================\n"

# Report worst setup violations
if {$setup_violation_count > 0} {
    puts "\n--- Worst 10 Setup Violations ---\n"
    set worst_setup [lrange [lsort -real -index 1 $setup_violations] 0 9]
    set idx 1
    foreach path $worst_setup {
        set slack [get_property $path slack]
        set from_pin [get_object_name [get_property $path from_pin]]
        set to_pin [get_object_name [get_property $path to_pin]]
        puts "  $idx. Slack: [format %.3f $slack] ps  From: $from_pin  To: $to_pin"
        incr idx
    }

    # Detailed report
    report_timing -delay_type max \
        -max_paths 10 \
        -slack_lesser_than 0 \
        -significant_digits 3 \
        -report_path_type full \
        -output $report_dir/critical_setup_paths.rpt
}

# Report worst hold violations
if {$hold_violation_count > 0} {
    puts "\n--- Worst 10 Hold Violations ---\n"
    set worst_hold [lrange [lsort -real -index 1 $hold_violations] 0 9]
    set idx 1
    foreach path $worst_hold {
        set slack [get_property $path slack]
        set from_pin [get_object_name [get_property $path from_pin]]
        set to_pin [get_object_name [get_property $path to_pin]]
        puts "  $idx. Slack: [format %.3f $slack] ps  From: $from_pin  To: $to_pin"
        incr idx
    }

    # Detailed report
    report_timing -delay_type min \
        -max_paths 10 \
        -slack_lesser_than 0 \
        -significant_digits 3 \
        -report_path_type full \
        -output $report_dir/critical_hold_paths.rpt
}

#===============================================================================
# Section 5: Clock Skew Analysis
#===============================================================================

puts "\n=========================================="
puts "Clock Skew Analysis"
puts "==========================================\n"

# Set clock timing margin
set_clock_timing_allow_margin 0.05

# Report clock skew
report_clock_timing -type skew -output $report_dir/clock_skew_analysis.rpt

# Calculate clock skew for each clock domain
set clocks {clk_core clk_npu clk_sys clk_mem}
foreach clk $clocks {
    puts "\n--- Clock Skew: $clk ---"
    set clk_pins [get_pins -of [get_clocks $clk] -filter "is_clock_pin"]
    if {[llength $clk_pins] > 0} {
        set min_latency [expr 1000000]
        set max_latency 0
        foreach pin $clk_pins {
            set latency [get_property [get_property $pin clock_latency] arrival_time]
            if {$latency < $min_latency} { set min_latency $latency }
            if {$latency > $max_latency} { set max_latency $latency }
        }
        set skew [expr $max_latency - $min_latency]
        puts "  Min Latency: [format %.3f $min_latency] ps"
        puts "  Max Latency: [format %.3f $max_latency] ps"
        puts "  Skew: [format %.3f $skew] ps"
    }
}

#===============================================================================
# Section 6: Path Group Analysis
#===============================================================================

puts "\n=========================================="
puts "Path Group Analysis"
puts "==========================================\n"

# Create path groups based on clock domains
group_path -name from_clk_core -from [get_clocks clk_core]
group_path -name from_clk_npu  -from [get_clocks clk_npu]
group_path -name from_clk_sys  -from [get_clocks clk_sys]
group_path -name from_clk_mem  -from [get_clocks clk_mem]

# Create path groups based on destination modules
group_path -name to_cpu_core -to [get_pins */cpu_core_inst/*]
group_path -name to_npu      -to [get_pins */npu_inst/*]
group_path -name to_ddr_ctrl -to [get_pins */ddr_ctrl_inst/*]
group_path -name to_periph   -to [get_pins */periph_inst/*]

# Report path groups
report_path_group -groups {from_clk_core from_clk_npu from_clk_sys from_clk_mem} \
    -output $report_dir/path_group_clock.rpt

report_path_group -groups {to_cpu_core to_npu to_ddr_ctrl to_periph} \
    -output $report_dir/path_group_module.rpt

#===============================================================================
# Section 7: Module-Level Timing Analysis
#===============================================================================

puts "\n=========================================="
puts "Module-Level Timing Analysis"
puts "==========================================\n"

# Define modules for analysis
set modules {
    cpu_core    {path */cpu_core_inst/* slack_threshold 0.1}
    npu         {path */npu_inst/* slack_threshold 0.1}
    axi_bus     {path */axi_bus_inst/* slack_threshold 0.1}
    ddr_ctrl    {path */ddr_ctrl_inst/* slack_threshold 0.1}
    periph_ctrl {path */periph_inst/* slack_threshold 0.1}
}

foreach module [array names modules] {
    puts "\n--- Module: $module ---"
    set module_path [dict get $modules($module) path]
    set threshold [dict get $modules($module) slack_threshold]

    # Count violations for this module
    set module_violations [get_timing_paths -to [get_pins $module_path] -slack_lesser_than 0]
    set module_violation_count [llength $module_violations]

    puts "  Violations: $module_violation_count"

    if {$module_violation_count > 0} {
        # Report worst violations for this module
        report_timing -max_paths 20 \
            -to [get_pins $module_path] \
            -slack_lesser_than $threshold \
            -output $report_dir/timing_${module}_violations.rpt
    }
}

#===============================================================================
# Section 8: Timing Budget Analysis
#===============================================================================

puts "\n=========================================="
puts "Timing Budget Analysis"
puts "==========================================\n"

# Analyze timing budgets for each clock domain
foreach clk $clocks {
    set clk_period [get_property [get_clocks $clk] period]
    puts "\n--- Clock: $clk (Period: ${clk_period} ps) ---"

    # Calculate timing budget
    set clock_uncertainty 0.05
    set setup_margin 0.10
    set hold_margin 0.05

    set setup_budget [expr $clk_period * (1 - $clock_uncertainty - $setup_margin)]
    set hold_budget [expr $clk_period * $hold_margin]

    puts "  Clock Uncertainty: [format %.3f [expr $clk_period * $clock_uncertainty]] ps"
    puts "  Setup Budget: [format %.3f $setup_budget] ps"
    puts "  Hold Budget: [format %.3f $hold_budget] ps"

    # Check if paths meet budget
    set clk_violations [get_timing_paths -from [get_clocks $clk] -slack_lesser_than 0]
    set clk_violation_count [llength $clk_violations]
    puts "  Path Violations: $clk_violation_count"
}

#===============================================================================
# Section 9: Optimization Recommendations
#===============================================================================

puts "\n=========================================="
puts "Optimization Recommendations"
puts "==========================================\n"

# Analyze violations and generate recommendations
set recommendations "Timing Closure Recommendations\n"
append recommendations "================================\n\n"

# Setup violation analysis
if {$setup_violation_count > 0} {
    append recommendations "Setup Violations: $setup_violation_count\n"
    append recommendations "Possible improvements:\n"
    append recommendations "  1. Check for high-fanout nets requiring buffer insertion\n"
    append recommendations "  2. Review critical path logic depth for restructuring\n"
    append recommendations "  3. Consider register retiming across pipeline stages\n"
    append recommendations "  4. Evaluate clock gating efficiency\n"
    append recommendations "  5. Check for unbalanced combinational logic\n\n"
}

# Hold violation analysis
if {$hold_violation_count > 0} {
    append recommendations "Hold Violations: $hold_violation_count\n"
    append recommendations "Possible improvements:\n"
    append recommendations "  1. Add delay cells on critical paths\n"
    append recommendations "  2. Check clock tree balancing\n"
    append recommendations "  3. Review hold margin in clock uncertainty\n"
    append recommendations "  4. Evaluate clock latency differences\n\n"
}

# Clock skew analysis
set clk_skew [get_property [get_clock_timing -type skew] skew]
if {$clk_skew > 50} {
    append recommendations "Clock Skew: [format %.3f $clk_skew] ps (HIGH)\n"
    append recommendations "Recommendations:\n"
    append recommendations "  1. Balance clock tree synthesis\n"
    append recommendations "  2. Review clock gating cell placement\n"
    append recommendations "  3. Check for routing congestion near clock roots\n\n"
}

# Write recommendations
set rec_file [open $report_dir/optimization_recommendations.rpt w]
puts $rec_file $recommendations
close $rec_file

puts $recommendations

#===============================================================================
# Section 10: Fix-Timing Commands Generation
#===============================================================================

puts "\n=========================================="
puts "Fix-Timing Commands"
puts "==========================================\n"

# Generate fix_timing commands for critical paths
set fix_commands "# YaoGuang SoC Fix-Timing Commands\n"
append fix_commands "# Generated: [clock format [clock seconds]]\n\n"

# Setup fixes
if {$setup_violation_count > 0} {
    append fix_commands "# Setup Violation Fixes\n"
    append fix_commands "#------------------------\n\n"

    foreach path [lrange $setup_violations 0 9] {
        set from_pin [get_object_name [get_property $path from_pin]]
        set to_pin [get_object_name [get_property $path to_pin]]
        append fix_commands "# Slack: [get_property $path slack] ps\n"
        append fix_commands "# Path: $from_pin -> $to_pin\n"
        append fix_commands "# Suggested fix: review logic between these points\n\n"
    }
}

# Write fix commands
set fix_file [open $report_dir/fix_timing_commands.tcl w]
puts $fix_file $fix_commands
close $fix_file

puts "[OK] Fix-timing commands saved to: $report_dir/fix_timing_commands.tcl"

#===============================================================================
# Section 11: Signoff Status
#===============================================================================

puts "\n=========================================="
puts "Timing Signoff Status"
puts "==========================================\n"

set total_violations [expr $setup_violation_count + $hold_violation_count + \
                      $recovery_violation_count + $removal_violation_count]

puts "Total Violations: $total_violations"
puts "  Setup:    $setup_violation_count"
puts "  Hold:     $hold_violation_count"
puts "  Recovery: $recovery_violation_count"
puts "  Removal:  $removal_violation_count"

if {$total_violations == 0} {
    puts "\n*** TIMING SIGNOFF: PASSED ***"
    set signoff_status "PASSED"
} else {
    puts "\n*** TIMING SIGNOFF: FAILED ***"
    puts "*** Revisions required before signoff ***"
    set signoff_status "FAILED"
}

#===============================================================================
# Section 12: Session Save
#===============================================================================

save_session $session_dir/timing_closure_session.session

puts "\n=========================================="
puts "Timing Closure Analysis Complete"
puts "==========================================\n"

puts "Reports generated in: $report_dir/"
puts "Session saved to: $session_dir/"

exit 0
