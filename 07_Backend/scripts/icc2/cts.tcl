#!/usr/bin/env tclsh
#===============================================================================
# YaoGuang SoC - Clock Tree Synthesis Script
#===============================================================================
# Version: V1.0
# Date: 2026-01-18
# Purpose: Clock Tree Synthesis for YaoGuang Auto-Grade SoC
# Process: TSMC 5nm
#===============================================================================

puts "=========================================================="
puts "Clock Tree Synthesis - Starting"
puts "=========================================================="

#===============================================================================
# 1. CTS Configuration
#===============================================================================

# Clock tree synthesis settings
set app_var clock_tree_synthesis true
set app_var cts_effort medium

# OCV settings for CTS
set_timing_derate -early 0.85
set_timing_derate -late 1.15

# CRPR settings
set_app_var enable_crpr true

puts "[INFO] CTS configuration set"

#===============================================================================
# 2. Clock Domain Analysis
#===============================================================================

puts "=========================================================="
puts "Clock Domain Analysis"
puts "=========================================================="

# Get all clocks
set all_clocks [get_clocks]
puts "[INFO] Total clocks: [sizeof $all_clocks]"

foreach clk $all_clocks {
  set clk_name [get_object_name $clk]
  set period [get_attribute $clk period]
  set sources [get_attribute $clk sources]
  puts "  - $clk_name: Period = ${period}ns, Sources = [llength $sources]"
}

# Identify clock domains
set clk_core [get_clocks -filter "name =~ *clk_core*"]
set clk_npu [get_clocks -filter "name =~ *clk_npu*"]
set clk_gpu [get_clocks -filter "name =~ *clk_gpu*"]
set clk_sys [get_clocks -filter "name =~ *clk_sys*"]
set clk_mem [get_clocks -filter "name =~ *clk_mem*"]
set clk_peri [get_clocks -filter "name =~ *clk_peri*"]

puts "[INFO] Clock domains identified"

#===============================================================================
# 3. CTS Specification File
#===============================================================================

puts "=========================================================="
puts "Creating CTS Specification"
puts "=========================================================="

# Create CTS specification file
set cts_spec_file /designs/yaoguang_soc/output/cts/cts.spec

# Generate CTS spec
create_clock_tree_spec \
  -output $cts_spec_file \
  -buffer_cells {CLKBUF_X1 CLKBUF_X2 CLKBUF_X4 CLKBUF_X8 CLKBUF_X16} \
  -inverter_cells {CLKINV_X1 CLKINV_X2 CLKINV_X4} \
  -max_fanout 32 \
  -max_level 12 \
  -min_level 2 \
  -target_skew 0.05 \
  -balance_levels true

puts "[INFO] CTS specification created: $cts_spec_file"

#===============================================================================
# 4. Clock Tree Constraints
#===============================================================================

puts "=========================================================="
puts "Setting Clock Tree Constraints"
puts "=========================================================="

# Set clock transition constraints
set_clock_tree_transition -clock clk_core -max_transition 0.2
set_clock_tree_transition -clock clk_npu -max_transition 0.2
set_clock_tree_transition -clock clk_gpu -max_transition 0.2
set_clock_tree_transition -clock clk_sys -max_transition 0.2
set_clock_tree_transition -clock clk_mem -max_transition 0.15
set_clock_tree_transition -clock clk_peri -max_transition 0.3

# Set target skew constraints
set_clock_tree_skew -clock clk_core -target_skew 0.05
set_clock_tree_skew -clock clk_npu -target_skew 0.05
set_clock_tree_skew -clock clk_gpu -target_skew 0.05
set_clock_tree_skew -clock clk_sys -target_skew 0.05
set_clock_tree_skew -clock clk_mem -target_skew 0.03
set_clock_tree_skew -clock clk_peri -target_skew 0.08

# Set clock latency constraints
set_clock_latency -source -clock clk_core -max 0.5
set_clock_latency -source -clock clk_npu -max 0.5
set_clock_latency -source -clock clk_mem -max 0.3

puts "[INFO] Clock tree constraints set"

#===============================================================================
# 5. CTS Exclusion Rules
#===============================================================================

puts "=========================================================="
puts "Setting CTS Exclusion Rules"
puts "=========================================================="

# Exclude non-clock pins
set_clock_tree_exceptions -pins [get_pins -filter "name =~ *test_mode*"]
set_clock_tree_exceptions -pins [get_pins -filter "name =~ *scan*"]

# Exclude specific instances from CTS
set_clock_tree_exceptions -instances [get_cells -filter "name =~ *pad_*"]]

# Exclude clock gating cells from balancing
set_clock_tree_exceptions -instances [get_cells -filter "name =~ *clock_gating*"]

puts "[INFO] CTS exclusion rules set"

#===============================================================================
# 6. Clock Gate Handling
#===============================================================================

puts "=========================================================="
puts "Configuring Clock Gate Handling"
puts "=========================================================="

# Identify clock gating cells
set clock_gates [get_cells -filter "is_clock_gating"]
puts "[INFO] Clock gating cells: [sizeof $clock_gates]"

# Set clock gate isolation
set_clock_gating_check -setup 0.1 -hold 0.05

# Balance clock gates
balance_clock_gates -effort high

puts "[INFO] Clock gate handling configured"

#===============================================================================
# 7. Execute Clock Tree Synthesis
#===============================================================================

puts "=========================================================="
puts "Executing Clock Tree Synthesis"
puts "=========================================================="

# Main CTS command
clock_design \
  -spec $cts_spec_file \
  -effort high \
  -balance_skew true \
  -route_clock_trees true

puts "[INFO] Clock tree synthesis completed"

#===============================================================================
# 8. CTS Quality Check
#===============================================================================

puts "=========================================================="
puts "CTS Quality Check"
puts "=========================================================="

# Report clock tree summary
report_clock_tree -summary

# Report clock skew
report_clock_tree -skew

# Report clock latency
report_clock_tree -latency

# Check for clock tree violations
check_clock_tree -verbose

puts "[INFO] CTS quality check completed"

#===============================================================================
# 9. Post-CTS Optimization
#===============================================================================

puts "=========================================================="
puts "Post-CTS Optimization"
puts "=========================================================="

# Optimize clock tree for timing
clock_opt_design \
  -effort high \
  -setup_targets 0.0 \
  -hold_targets 0.0 \
  -skew_targets 0.05

puts "[INFO] Post-CTS optimization completed"

#===============================================================================
# 10. CTS Timing Report
#===============================================================================

puts "=========================================================="
puts "CTS Timing Report"
puts "=========================================================="

# Report clock timing
report_clock_timing -type skew
report_clock_timing -type latency
report_clock_timing -type transition

# Report worst setup/hold after CTS
report_timing -max_paths 10 -nworst 5 -delay_type max
report_timing -max_paths 10 -nworst 5 -delay_type min

#===============================================================================
# 11. Save CTS Database
#===============================================================================

puts "=========================================================="
puts "Saving CTS Database"
puts "=========================================================="

# Save Milkyway database
save_mw_cel -as yaoguang_soc_cts

# Save DEF with clock routes
write_def -version 5.8 -output /designs/yaoguang_soc/output/pnr/yaoguang_soc_cts.def

# Write clock tree spec report
report_clock_tree -output /designs/yaoguang_soc/output/cts/clock_tree_report.rpt

puts "[INFO] CTS database saved"

puts "[INFO] Clock Tree Synthesis completed successfully"
puts "=========================================================="
