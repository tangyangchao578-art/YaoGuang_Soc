#!/usr/bin/env tclsh
#===============================================================================
# YaoGuang SoC - Placement Script
#===============================================================================
# Version: V1.0
# Date: 2026-01-18
# Purpose: Standard cell placement for YaoGuang Auto-Grade SoC
#===============================================================================

puts "=========================================================="
puts "Placement - Starting"
puts "=========================================================="

#===============================================================================
# 1. Placement Configuration
#===============================================================================

# Set placement effort
set_placement_effort medium

# Enable timing-driven placement
set_app_var place_opt_effort high

# Set timing derate for OCV
set_timing_derate -early 0.9
set_timing_derate -late 1.1

puts "[INFO] Placement configuration set"

#===============================================================================
# 2. Pre-Placement Checks
#===============================================================================

puts "=========================================================="
puts "Pre-Placement Checks"
puts "=========================================================="

# Check for unplaced instances
set unplaced [get_cells -filter "!is_placed"]
puts "[INFO] Unplaced instances before placement: [sizeof $unplaced]"

# Check for high-fanout nets
set hfn [get_nets -filter "fanout >= 64"]
puts "[INFO] High-fanout nets (fanout >= 64): [sizeof $hfn]"

# Report critical paths
report_timing -max_paths 10 -nworst 1

#===============================================================================
# 3. Initial Placement
#===============================================================================

puts "=========================================================="
puts "Initial Placement"
puts "=========================================================="

# Perform initial placement
initialize_placement \
  -timing_driven true \
  -incremental true \
  -effort high

puts "[INFO] Initial placement completed"

#===============================================================================
# 4. Standard Cell Placement
#===============================================================================

puts "=========================================================="
puts "Standard Cell Placement"
puts "=========================================================="

# Main placement command
place_design \
  -effort high \
  -timing_driven true \
  -congestion_driven true \
  -routability_driven true

puts "[INFO] Standard cell placement completed"

#===============================================================================
# 5. Placement Optimization
#===============================================================================

puts "=========================================================="
puts "Placement Optimization"
puts "=========================================================="

# Optimize placement for timing
place_opt_design \
  -effort high \
  -setup_targets 0.0 \
  -hold_targets 0.0

puts "[INFO] Placement optimization completed"

#===============================================================================
# 6. High-Fanout Net Synthesis
#===============================================================================

puts "=========================================================="
puts "High-Fanout Net Synthesis"
puts "=========================================================="

# Optimize high-fanout nets
set hfn_targets [get_nets -filter "fanout >= 64 && !is_clock"]
if {[sizeof $hfn_targets] > 0} {
  synthesize_buffers -nets $hfn_targets \
    -buffer_cells {BUF_X1 BUF_X2 BUF_X4 BUF_X8} \
    -max_fanout 32
  
  puts "[INFO] High-fanout nets synthesized: [sizeof $hfn_targets]"
}

#===============================================================================
# 7. Tie Cell Placement
#===============================================================================

puts "=========================================================="
puts "Tie Cell Placement"
puts "=========================================================="

# Place tie cells
insert_tiecells -library [get_libs * -filter "name =~ *stdcell*"] \
  -prefix "TIEOFF_"

puts "[INFO] Tie cells inserted"

#===============================================================================
# 8. Filler Cell Placement
#===============================================================================

puts "=========================================================="
puts "Filler Cell Placement"
puts "=========================================================="

# Add standard cell fillers
insert_filler \
  -cells {FILL_X1 FILL_X2 FILL_X4 FILL_X8 FILL_X16} \
  -core

# Add decoupling capacitors
insert_decap \
  -cells {DECAP_X1 DECAP_X2 DECAP_X4 DECAP_X8} \
  -max_capacity 100

puts "[INFO] Filler cells and decaps placed"

#===============================================================================
# 9. Placement Legality Check
#===============================================================================

puts "=========================================================="
puts "Placement Legality Check"
puts "=========================================================="

# Check for placement violations
check_placement -verbose

# Fix any placement violations
if {[sizeof [get_cells -filter "is_placed && is_illegal]] > 0} {
  puts "[WARNING] Illegal placements found, fixing..."
  fix_placement -all
}

puts "[INFO] Placement legality check completed"

#===============================================================================
# 10. Placement Quality Report
#===============================================================================

puts "=========================================================="
puts "Placement Quality Report"
puts "=========================================================="

# Report placement statistics
set placed_cells [get_cells -filter "is_placed"]
set total_cells [get_cells]

puts "[INFO] Placement Statistics:"
puts "  - Total cells: [sizeof $total_cells]"
puts "  - Placed cells: [sizeof $placed_cells]"
puts "  - Placement density: [format %.2f [expr 100.0 * [sizeof $placed_cells] / [sizeof $total_cells]]]%"

# Report timing
report_timing -max_paths 20 -nworst 5

# Report area
report_area

# Report congestion
report_congestion -verbose

#===============================================================================
# 11. Critical Path Analysis
#===============================================================================

puts "=========================================================="
puts "Critical Path Analysis"
puts "=========================================================="

# Get worst setup path
set worst_setup_path [report_timing -delay_type max -max_paths 1 -nworst 1]
puts "[INFO] Worst setup slack: [get_timing_paths -delay_type max -max_paths 1 -nworst 1]"

# Get worst hold path
set worst_hold_path [report_timing -delay_type min -max_paths 1 -nworst 1]
puts "[INFO] Worst hold slack: [get_timing_paths -delay_type min -max_paths 1 -nworst 1]"

#===============================================================================
# 12. Save Placement Database
#===============================================================================

puts "=========================================================="
puts "Saving Placement Database"
puts "=========================================================="

# Save Milkyway database
save_mw_cel -as yaoguang_soc_placed

# Save DEF
write_def -version 5.8 -output /designs/yaoguang_soc/output/pnr/yaoguang_soc_placed.def

puts "[INFO] Placement database saved"

puts "[INFO] Placement completed successfully"
puts "=========================================================="
