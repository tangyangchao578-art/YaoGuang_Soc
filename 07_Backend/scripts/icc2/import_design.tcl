#!/usr/bin/env tclsh
#===============================================================================
# YaoGuang SoC - Design Import Script
#===============================================================================
# Version: V1.0
# Date: 2026-01-18
# Purpose: Import design, constraints, and setup for ICC2 P&R flow
#===============================================================================

puts "=========================================================="
puts "Design Import - Starting"
puts "=========================================================="

#===============================================================================
# 1. Design Import Configuration
#===============================================================================

# Design name and top module
set design_name "yaoguang_soc_top"
set netlist_file "/designs/yaoguang_soc/output/syn/yaoguang_soc_netlist.v"
set top_module "yaoguang_soc_top"

puts "[INFO] Design: $design_name"
puts "[INFO] Netlist: $netlist_file"

#===============================================================================
# 2. Check Design Library
#===============================================================================

# Verify library exists
set current_lib [current_lib]
puts "[INFO] Current library: $current_lib"

# List available cells
puts "[INFO] Available cells in library:"
foreach cell [get_libs $current_lib -filter "cell_type == stdcell"] {
  puts "  - $cell"
}

#===============================================================================
# 3. Import Verilog Netlist
#===============================================================================

puts "=========================================================="
puts "Importing Verilog Netlist..."
puts "=========================================================="

# Check if netlist exists
if {![file exists $netlist_file]} {
  puts "[ERROR] Netlist file not found: $netlist_file"
  exit 1
}

# Read the Verilog netlist
import_designs $netlist_file \
  -format verilog \
  -top $top_module

# Set current design
current_design $design_name

# Link the design
link

puts "[INFO] Netlist imported successfully"

#===============================================================================
# 4. Design Information
#===============================================================================

puts "=========================================================="
puts "Design Statistics"
puts "=========================================================="

# Report instance count
set inst_count [get_designs -filter "name == $design_name" -quiet]
if {$inst_count ne ""} {
  set instance_count [sizeof [all_registers -clock_tree]]
  puts "[INFO] Total instances: [sizeof [all_instances]]"
  puts "[INFO] Total nets: [sizeof [all_nets]]"
  puts "[INFO] Total pins: [sizeof [all_pins]]"
  
  # Report clock domains
  set clock_nets [get_clocks -quiet]
  puts "[INFO] Clock domains: [llength $clock_nets]"
  foreach clk $clock_nets {
    puts "  - [get_object_name $clk]"
  }
  
  # Report sequential elements
  set flops [get_cells -filter "is_sequential"]
  puts "[INFO] Sequential elements: [sizeof $flops]"
  
  # Report combinational cells
  set comb [get_cells -filter "!is_sequential"]
  puts "[INFO] Combinational elements: [sizeof $comb]"
}

#===============================================================================
# 5. Hierarchy Information
#===============================================================================

puts "=========================================================="
puts "Hierarchy Information"
puts "=========================================================="

# Report hierarchy
report_hierarchy -level all

#===============================================================================
# 6. IO Port Information
#===============================================================================

puts "=========================================================="
puts "IO Port Information"
puts "=========================================================="

# Input ports
set inputs [get_ports -filter "direction == in"]
puts "[INFO] Input ports: [sizeof $inputs]"

# Output ports
set outputs [get_ports -filter "direction == out"]
puts "[INFO] Output ports: [sizeof $outputs]"

# Bidirectional ports
set bidirs [get_ports -filter "direction == inout"]
puts "[INFO] Bidirectional ports: [sizeof $bidirs]"

# Clock ports
set clk_ports [get_ports -filter "clock"]
puts "[INFO] Clock ports: [sizeof $clk_ports]"

#===============================================================================
# 7. Power Domain Information
#===============================================================================

puts "=========================================================="
puts "Power Domain Information"
puts "=========================================================="

# Get power domains
set power_domains [get_power_domains -quiet]
if {$power_domains ne ""} {
  puts "[INFO] Power domains found:"
  foreach pd $power_domains {
    puts "  - [get_object_name $pd]"
  }
} else {
  puts "[INFO] No power domains defined yet"
}

#===============================================================================
# 8. Black Box Modules
#===============================================================================

puts "=========================================================="
puts "Black Box Modules"
puts "=========================================================="

# Check for black boxes
set black_boxes [get_cells -filter "is_black_box"]
if {[sizeof $black_boxes] > 0} {
  puts "[INFO] Black box modules:"
  foreach bb $black_boxes {
    puts "  - [get_object_name $bb]"
  }
} else {
  puts "[INFO] No black box modules found"
}

#===============================================================================
# 9. Timing Constraints Summary
#===============================================================================

puts "=========================================================="
puts "Timing Constraints Summary"
puts "=========================================================="

# Report clocks
puts "[INFO] Clocks:"
foreach clk [get_clocks] {
  set period [get_attribute $clk period]
  set sources [get_attribute $clk sources]
  puts "  - [get_object_name $clk]: Period = $period ns"
}

# Report timing exceptions
set multicycles [get_multicycle_paths -quiet]
if {[sizeof $multicycles] > 0} {
  puts "[INFO] Multi-cycle paths: [sizeof $multicycles]"
}

set false_paths [get_false_paths -quiet]
if {[sizeof $false_paths] > 0} {
  puts "[INFO] False paths: [sizeof $false_paths]"
}

#===============================================================================
# 10. Design Rule Checks
#===============================================================================

puts "=========================================================="
puts "Pre-Import Design Rule Checks"
puts "=========================================================="

# Run basic design checks
check_design -unconnected

puts "[INFO] Design import completed successfully"
puts "=========================================================="
