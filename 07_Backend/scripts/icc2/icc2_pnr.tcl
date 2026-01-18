#!/usr/bin/env tclsh
#===============================================================================
# YaoGuang SoC ICC2 P&R Main Script
#===============================================================================
# Version: V1.0
# Date: 2026-01-18
# Author: Backend Engineering Team
# Purpose: Complete P&R flow for YaoGuang Auto-Grade SoC
# Process: TSMC 5nm
# Die Size: 15mm x 15mm
#===============================================================================

#===============================================================================
# 1. Environment Setup
#===============================================================================
puts "=========================================================="
puts "YaoGuang SoC ICC2 P&R Flow - Starting"
puts "=========================================================="
puts "[INFO] Initializing ICC2 environment..."

# Set Synopsys auto setup
set_synopsys_auto_setup true

# Configure license
set_app_var snpslicense_mode SNPSLMD_LICENSE_FILE

# Set search paths
set_app_var search_path "\
  /pdk/tsmc5nm/lef \
  /pdk/tsmc5nm/tf \
  /libs/stdcell \
  /libs/macros \
  /designs/yaoguang_soc/constraints \
  ."

# Set symbol library
set_app_var symbol_library "generic.sdb"

# Set link library
set_app_var link_library "\
  * \
  standard_cell_library.db \
  cpu_cortex_a78ae.db \
  cpu_cortex_r52.db \
  npu_cluster.db \
  mali_gpu.db \
  isp.db \
  ddr_controller.db \
  pcie_controller.db \
  usb_controller.db"

# Set target library
set_app_var target_library "standard_cell_library.db"

# Set physical constraint file
set_app_var pcf_file "yaoguang_soc.pcf"

# Set timing window
set_app_var timing_enable_multiple_clocks true

puts "[INFO] Environment setup completed"

#===============================================================================
# 2. Library Creation
#===============================================================================
puts "=========================================================="
puts "Step 1: Creating Design Library"
puts "=========================================================="

# Define library name
set lib_name "yaoguang_soc_lib"

# Remove existing library if present
if {[lib_exists $lib_name]} {
  puts "[WARNING] Library $lib_name exists, removing..."
  remove_lib $lib_name
}

# Create main library
create_lib $lib_name \
  -tech /pdk/tsmc5nm/tf/tech.tf \
  -ref_libs {\
    /libs/stdcell/stdcell.lef \
    /libs/macros/cortex_a78ae.lef \
    /libs/macros/cortex_r52.lef \
    /libs/macros/npu_cluster.lef \
    /libs/macros/mali_g78.lef \
    /libs/macros/isp.lef \
    /libs/macros/ddr_controller.lef \
    /libs/macros/pcie_controller.lef \
    /libs/macros/usb_controller.lef \
    /libs/macros/l3_cache.lef \
  } \
  -lef /designs/yaoguang_soc/output/yaoguang_soc.lef \
  -mw_logic_block

# Configure library settings
set_lib $lib_name \
  -default_typ_delay 1.0 \
  -delay_model table \
  -wire_load_mode enclosed

# Set OCV/CRPR settings
set_app_var enable_ocv true
set_app_var enable_crpr true

puts "[INFO] Library $lib_name created successfully"

#===============================================================================
# 3. Design Import
#===============================================================================
puts "=========================================================="
puts "Step 2: Importing Design"
puts "=========================================================="

# Set current library
current_lib $lib_name

# Source design import script
source /designs/yaoguang_soc/scripts/icc2/import_design.tcl

puts "[INFO] Design import completed"

#===============================================================================
# 4. Constraint Import
#===============================================================================
puts "=========================================================="
puts "Step 3: Importing Constraints"
puts "=========================================================="

# Read SDC constraints
if {[file exists /designs/yaoguang_soc/constraints/yaoguang_soc_sdc.out.sdc]} {
  read_sdc /designs/yaoguang_soc/constraints/yaoguang_soc_sdc.out.sdc
  puts "[INFO] SDC constraints loaded"
} else {
  puts "[ERROR] SDC file not found!"
  exit 1
}

# Read UPF for power intent
if {[file exists /designs/yaoguang_soc/constraints/yaoguang_soc.upf]} {
  read_upf /designs/yaoguang_soc/constraints/yaoguang_soc.upf
  puts "[INFO] UPF power intent loaded"
} else {
  puts "[WARNING] UPF file not found, using default power intent"
}

# Read Multi-Voltage constraints
if {[file exists /designs/yaoguang_soc/constraints/yaoguang_soc.mv]} {
  read_mv /designs/yaoguang_soc/constraints/yaoguang_soc.mv
  puts "[INFO] Multi-Voltage constraints loaded"
}

#===============================================================================
# 5. Floorplan
#===============================================================================
puts "=========================================================="
puts "Step 4: Creating Floorplan"
puts "=========================================================="

source /designs/yaoguang_soc/scripts/icc2/floorplan.tcl

puts "[INFO] Floorplan completed"

#===============================================================================
# 6. Placement
#===============================================================================
puts "=========================================================="
puts "Step 5: Standard Cell Placement"
puts "=========================================================="

source /designs/yaoguang_soc/scripts/icc2/placement.tcl

puts "[INFO] Placement completed"

#===============================================================================
# 7. CTS
#===============================================================================
puts "=========================================================="
puts "Step 6: Clock Tree Synthesis"
puts "=========================================================="

source /designs/yaoguang_soc/scripts/icc2/cts.tcl

puts "[INFO] CTS completed"

#===============================================================================
# 8. Routing
#===============================================================================
puts "=========================================================="
puts "Step 7: Global and Detailed Routing"
puts "=========================================================="

source /designs/yaoguang_soc/scripts/icc2/routing.tcl

puts "[INFO] Routing completed"

#===============================================================================
# 9. Optimization
#===============================================================================
puts "=========================================================="
puts "Step 8: Post-Route Optimization"
puts "=========================================================="

source /designs/yaoguang_soc/scripts/icc2/optimization.tcl

puts "[INFO] Optimization completed"

#===============================================================================
# 10. Output Generation
#===============================================================================
puts "=========================================================="
puts "Step 9: Generating Output Files"
puts "=========================================================="

# Create output directory
set output_dir /designs/yaoguang_soc/output/pnr_results
file mkdir $output_dir

# Write DEF
puts "[INFO] Writing DEF file..."
write_def -version 5.8 -output $output_dir/yaoguang_soc_pnr.def

# Write Verilog netlist
puts "[INFO] Writing Verilog netlist..."
write_verilog -output $output_dir/yaoguang_soc_pnr.v

# Write SPEF for signoff
puts "[INFO] Writing SPEF file..."
write_parasitics -spef_file $output_dir/yaoguang_soc_pnr.spef

# Write SDC for signoff
puts "[INFO] Writing SDC file..."
write_sdc -nosplit $output_dir/yaoguang_soc_pnr.sdc

# Write GDSII
puts "[INFO] Writing GDSII file..."
write_gdsii -output $output_dir/yaoguang_soc_pnr.gds

# Generate reports
puts "[INFO] Generating reports..."

# Timing report
report_timing -max_paths 50 > $output_dir/timing_report.rpt

# Power report
report_power -hier > $output_dir/power_report.rpt

# Area report
report_area -hierarchy > $output_dir/area_report.rpt

# DRC report
report_design_rule_check > $output_dir/drc_report.rpt

# Clock tree report
report_clock_tree -summary > $output_dir/cts_report.rpt

puts "[INFO] All output files generated successfully"

#===============================================================================
# 11. Summary
#===============================================================================
puts "=========================================================="
puts "YaoGuang SoC P&R Flow Completed Successfully!"
puts "=========================================================="
puts ""
puts "Output Files:"
puts "  - DEF: $output_dir/yaoguang_soc_pnr.def"
puts "  - Verilog: $output_dir/yaoguang_soc_pnr.v"
puts "  - SPEF: $output_dir/yaoguang_soc_pnr.spef"
puts "  - GDSII: $output_dir/yaoguang_soc_pnr.gds"
puts ""
puts "Reports:"
puts "  - Timing: $output_dir/timing_report.rpt"
puts "  - Power: $output_dir/power_report.rpt"
puts "  - Area: $output_dir/area_report.rpt"
puts "  - DRC: $output_dir/drc_report.rpt"
puts "  - CTS: $output_dir/cts_report.rpt"
puts "=========================================================="

# Exit cleanly
exit 0
