#!/usr/bin/env tclsh
#===============================================================================
# YaoGuang SoC - Routing Script
#===============================================================================
# Version: V1.0
# Date: 2026-01-18
# Purpose: Global and Detailed Routing for YaoGuang Auto-Grade SoC
# Process: TSMC 5nm
#===============================================================================

puts "=========================================================="
puts "Routing - Starting"
puts "=========================================================="

#===============================================================================
# 1. Routing Configuration
#===============================================================================

# Enable SI-aware routing
set_app_var siAwareRouter true

# Set routing effort
set_app_var router_effort high

# Set timing-driven routing
set_app_var timing_driven_routing true

# Enable antenna checking during routing
set_app_var router_antenna_check true

puts "[INFO] Routing configuration set"

#===============================================================================
# 2. Pre-Routing Checks
#===============================================================================

puts "=========================================================="
puts "Pre-Routing Checks"
puts "=========================================================="

# Check for design rule violations
check_design -rules drc

# Check for unconnected nets
check_design -unconnected

# Report timing before routing
report_timing -max_paths 20 -nworst 5 -delay_type max

# Check clock tree
report_clock_tree -summary

puts "[INFO] Pre-routing checks completed"

#===============================================================================
# 3. Special Routing (Power and Clock)
#===============================================================================

puts "=========================================================="
puts "Special Routing (Power and Clock)"
puts "=========================================================="

# Route power and ground nets
route_special -connect {corePin blockPin padPin} \
  -layer_change_range {M1 M10} \
  -automatic true \
  -power_net VDD \
  -ground_net VSS

puts "[INFO] Power and ground nets routed"

# Route clock nets
route_special -connect {clockTreePin} \
  -layer_change_range {M1 M10} \
  -automatic true \
  -nets [get_clocks]

puts "[INFO] Clock nets routed"

#===============================================================================
# 4. Global Routing
#===============================================================================

puts "=========================================================="
puts "Global Routing"
puts "=========================================================="

# Set global routing parameters
set_global_routing_density -high 0.9
set_global_routing_density -low 0.5
set_global_routing_space_scale_factor 1.0

# Enable timing-driven global routing
set_global_routing_timing_effort high

# Execute global routing
global_route -timing_driven true -congestion_driven true

puts "[INFO] Global routing completed"

# Report global routing congestion
report_global_routing -congestion

#===============================================================================
# 5. Track Assignment
#===============================================================================

puts "=========================================================="
puts "Track Assignment"
puts "=========================================================="

# Perform track assignment
assign_tracks

puts "[INFO] Track assignment completed"

#===============================================================================
# 6. Detailed Routing
#===============================================================================

puts "=========================================================="
puts "Detailed Routing"
puts "=========================================================="

# Main routing command
route_design \
  -unidirectional \
  -timing_driven true \
  -crosstalk_driven true \
  -antenna_driven true \
  -effort high

puts "[INFO] Detailed routing completed"

#===============================================================================
# 7. Routing Optimization
#===============================================================================

puts "=========================================================="
puts "Routing Optimization"
puts "=========================================================="

# Optimize routing for timing and SI
route_opt_design \
  -effort high \
  -setup_targets 0.0 \
  -hold_targets 0.0 \
  -si_aware true \
  -antenna_fix true

puts "[INFO] Routing optimization completed"

#===============================================================================
# 8. Signal Integrity Analysis
#===============================================================================

puts "=========================================================="
puts "Signal Integrity Analysis"
puts "=========================================================="

# Enable SI analysis
set_si_enable_analysis true
set_si_enable_propagation true

# Run SI analysis
check_si_timing -verbose

# Fix SI violations
if {[sizeof [get_nets -filter "crosstalk_violation"]] > 0} {
  fix_si_timing -effort high
}

puts "[INFO] Signal integrity analysis completed"

#===============================================================================
# 9. Antenna Check
#===============================================================================

puts "=========================================================="
puts "Antenna Check"
puts "=========================================================="

# Check for antenna violations
check_antenna

# Fix antenna violations if any
if {[sizeof [get_antenna_violations]] > 0} {
  insert_antenna_diodes -library [get_libs * -filter "name =~ *stdcell*"]
}

puts "[INFO] Antenna check completed"

#===============================================================================
# 10. DRC Fix
#===============================================================================

puts "=========================================================="
puts "DRC Fix"
puts "=========================================================="

# Check for routing DRC violations
check_design -rules drc

# Fix DRC violations
fix_routing_drc -effort high

puts "[INFO] DRC fix completed"

#===============================================================================
# 11. Final Routing Report
#===============================================================================

puts "=========================================================="
puts "Final Routing Report"
puts "=========================================================="

# Report routing statistics
report_route -summary

# Report wire length
report_wire_length

# Report via count
report_via_count

# Report timing
report_timing -max_paths 50 -nworst 10 -delay_type max
report_timing -max_paths 50 -nworst 10 -delay_type min

# Report DRC
report_design_rule_check

# Report SI
report_si_timing

#===============================================================================
# 12. Save Routing Database
#===============================================================================

puts "=========================================================="
puts "Saving Routing Database"
puts "=========================================================="

# Save Milkyway database
save_mw_cel -as yaoguang_soc_routed

# Save DEF
write_def -version 5.8 -output /designs/yaoguang_soc/output/pnr/yaoguang_soc_routed.def

# Save Verilog netlist
write_verilog -output /designs/yaoguang_soc/output/pnr/yaoguang_soc_routed.v

puts "[INFO] Routing database saved"

puts "[INFO] Routing completed successfully"
puts "=========================================================="
