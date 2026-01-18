#!/usr/bin/env tclsh
#===============================================================================
# YaoGuang SoC - Post-Route Optimization Script
#===============================================================================
# Version: V1.0
# Date: 2026-01-18
# Purpose: Final optimization for timing, power, and signoff
# Process: TSMC 5nm
#===============================================================================

puts "=========================================================="
puts "Post-Route Optimization - Starting"
puts "=========================================================="

#===============================================================================
# 1. Optimization Configuration
#===============================================================================

# Enable OCV/CRPR
set_app_var enable_ocv true
set_app_var enable_crpr true

# Set derate values
set_timing_derate -early 0.85
set_timing_derate -late 1.15

# Enable power optimization
set_app_var power_enable_analysis true
set_app_var power_analysis_mode average

puts "[INFO] Optimization configuration set"

#===============================================================================
# 2. Pre-Optimization Checks
#===============================================================================

puts "=========================================================="
puts "Pre-Optimization Analysis"
puts "=========================================================="

# Check for DRC violations
check_design -rules drc
set drc_count [sizeof [get_drc_violations]]
puts "[INFO] DRC violations: $drc_count"

# Check for timing violations
report_timing -max_paths 100 -nworst 10 -delay_type max
set setup_violations [get_timing_paths -delay_type max -slack_lesser_than 0]
puts "[INFO] Setup violations: [sizeof $setup_violations]"

report_timing -max_paths 100 -nworst 10 -delay_type min
set hold_violations [get_timing_paths -delay_type min -slack_lesser_than 0]
puts "[INFO] Hold violations: [sizeof $hold_violations]"

# Check for SI violations
set_si_enable_analysis true
check_si_timing
set si_violations [get_nets -filter "crosstalk_violation"]
puts "[INFO] SI violations: [sizeof $si_violations]"

# Check power
report_power -hier
set leakage_power [get_power -type leakage]
set dynamic_power [get_power -type dynamic]
puts "[INFO] Leakage Power: ${leakage_power}W"
puts "[INFO] Dynamic Power: ${dynamic_power}W"

#===============================================================================
# 3. Setup Time Optimization
#===============================================================================

puts "=========================================================="
puts "Setup Time Optimization"
puts "=========================================================="

# Post-route setup optimization
time_design -post_route -setup \
  -effort high \
  -slack_target 0.0 \
  -incremental true

puts "[INFO] Setup optimization completed"

# Verify setup
set setup_violations_after [get_timing_paths -delay_type max -slack_lesser_than 0]
puts "[INFO] Setup violations after optimization: [sizeof $setup_violations_after]"

#===============================================================================
# 4. Hold Time Optimization
#===============================================================================

puts "=========================================================="
puts "Hold Time Optimization"
puts "=========================================================="

# Post-route hold optimization
time_design -post_route -hold \
  -effort high \
  -slack_target 0.0 \
  -incremental true

puts "[INFO] Hold optimization completed"

# Verify hold
set hold_violations_after [get_timing_paths -delay_type min -slack_lesser_than 0]
puts "[INFO] Hold violations after optimization: [sizeof $hold_violations_after]"

#===============================================================================
# 5. Signal Integrity Optimization
#===============================================================================

puts "=========================================================="
puts "Signal Integrity Optimization"
puts "=========================================================="

# SI-aware optimization
route_opt_design \
  -si_aware true \
  -effort high

# Crosstalk fixing
fix_si_timing -effort high

puts "[INFO] SI optimization completed"

# Verify SI
check_si_timing
set si_violations_after [get_nets -filter "crosstalk_violation"]
puts "[INFO] SI violations after optimization: [sizeof $si_violations_after]"

#===============================================================================
# 6. Power Optimization
#===============================================================================

puts "=========================================================="
puts "Power Optimization"
puts "=========================================================="

# Enable leakage power optimization
set_power_optimization -leakage true

# Multi-Vt optimization
set_multi_voltage_optimization -effort high

# Clock gating optimization
optimize_clock_gating -effort high

# Report power after optimization
report_power -hier

puts "[INFO] Power optimization completed"

#===============================================================================
# 7. Area Optimization
#===============================================================================

puts "=========================================================="
puts "Area Optimization"
puts "=========================================================="

# Area optimization
resize_design -effort high

# Report area
report_area -hierarchy

puts "[INFO] Area optimization completed"

#===============================================================================
# 8. Timing Closure Iterations
#===============================================================================

puts "=========================================================="
puts "Timing Closure Iterations"
puts "=========================================================="

# Iterative timing closure
set max_iterations 10
set iteration 0
set converged false

while {$iteration < $max_iterations && !$converged} {
  incr iteration
  puts "=========================================="
  puts "Timing Closure Iteration $iteration of $max_iterations"
  puts "=========================================="
  
  # Run optimization
  time_design -post_route \
    -setup \
    -hold \
    -effort high \
    -incremental true
  
  # Check violations
  set setup_violations [get_timing_paths -delay_type max -slack_lesser_than 0]
  set hold_violations [get_timing_paths -delay_type min -slack_lesser_than 0]
  
  puts "[INFO] Setup violations: [sizeof $setup_violations]"
  puts "[INFO] Hold violations: [sizeof $hold_violations]"
  
  # Check if converged
  if {[sizeof $setup_violations] == 0 && [sizeof $hold_violations] == 0} {
    set converged true
    puts "[INFO] Timing converged after $iteration iterations!"
  }
}

if {!$converged} {
  puts "[WARNING] Timing did not converge after $max_iterations iterations"
}

#===============================================================================
# 9. Final Signoff Checks
#===============================================================================

puts "=========================================================="
puts "Final Signoff Checks"
puts "=========================================================="

# Final timing report
report_timing -max_paths 100 -nworst 20 -delay_type max > /designs/yaoguang_soc/output/reports/timing_setup_final.rpt
report_timing -max_paths 100 -nworst 20 -delay_type min > /designs/yaoguang_soc/output/reports/timing_hold_final.rpt

# Final power report
report_power -hier > /designs/yaoguang_soc/output/reports/power_final.rpt

# Final area report
report_area -hierarchy > /designs/yaoguang_soc/output/reports/area_final.rpt

# Final DRC check
check_design -rules drc > /designs/yaoguang_soc/output/reports/drc_final.rpt

# Final SI check
report_si_timing > /designs/yaoguang_soc/output/reports/si_final.rpt

#===============================================================================
# 10. Timing Signoff Summary
#===============================================================================

puts "=========================================================="
puts "Timing Signoff Summary"
puts "=========================================================="

# WNS and TNS
set wns_setup [get_timing_analysis -delay_type max -wns]
set tns_setup [get_timing_analysis -delay_type max -tns]
set wns_hold [get_timing_analysis -delay_type min -wns]
set tns_hold [get_timing_analysis -delay_type min -tns]

puts "Setup Analysis:"
puts "  - Worst Negative Slack (WNS): ${wns_setup}ns"
puts "  - Total Negative Slack (TNS): ${tns_setup}ns"

puts "Hold Analysis:"
puts "  - Worst Negative Slack (WNS): ${wns_hold}ns"
puts "  - Total Negative Slack (TNS): ${tns_hold}ns"

# Critical paths
puts ""
puts "Top 10 Critical Paths (Setup):"
foreach path [get_timing_paths -delay_type max -max_paths 10] {
  set slack [get_attribute $path slack]
  set start [get_attribute $path start_point]
  set end [get_attribute $path end_point]
  puts "  Slack: ${slack}ns, Start: $start, End: $end"
}

#===============================================================================
# 11. Power Signoff Summary
puts "=========================================================="
puts "Power Signoff Summary"
puts "=========================================================="

# Power breakdown
report_power -analysis_mode average -hier

# Power by domain
report_power -domains

#===============================================================================
# 12. Save Final Database
#===============================================================================

puts "=========================================================="
puts "Saving Final Database"
puts "=========================================================="

# Save Milkyway database
save_mw_cel -as yaoguang_soc_signoff

# Save DEF
write_def -version 5.8 -output /designs/yaoguang_soc/output/pnr/yaoguang_soc_signoff.def

# Save Verilog netlist
write_verilog -output /designs/yaoguang_soc/output/pnr/yaoguang_soc_signoff.v

# Save SPEF for PrimeTime signoff
write_parasitics -spef_file /designs/yaoguang_soc/output/pnr/yaoguang_soc_signoff.spef

# Save SDC
write_sdc -nosplit /designs/yaoguang_soc/output/pnr/yaoguang_soc_signoff.sdc

puts "[INFO] Final database saved"

#===============================================================================
# 13. Final Summary
#===============================================================================

puts "=========================================================="
puts "Post-Route Optimization Completed"
puts "=========================================================="
puts ""
puts "Design: yaoguang_soc_top"
puts "Process: TSMC 5nm"
puts ""
puts "Signoff Results:"
puts "  - Setup WNS: ${wns_setup}ns"
puts "  - Hold WNS: ${wns_hold}ns"
puts "  - Total Power: [get_power -total]W"
puts "  - DRC Violations: $drc_count"
puts ""
puts "Output Files:"
puts "  - DEF: yaoguang_soc_signoff.def"
puts "  - Verilog: yaoguang_soc_signoff.v"
puts "  - SPEF: yaoguang_soc_signoff.spef"
puts "  - SDC: yaoguang_soc_signoff.sdc"
puts "=========================================================="

# Exit cleanly
exit 0
