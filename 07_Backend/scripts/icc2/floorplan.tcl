#!/usr/bin/env tclsh
#===============================================================================
# YaoGuang SoC - Floorplan Script
#===============================================================================
# Version: V1.0
# Date: 2026-01-18
# Purpose: Create floorplan for YaoGuang Auto-Grade SoC
# Process: TSMC 5nm
# Die Size: 15mm x 15mm
# Core Size: 12mm x 12mm
#===============================================================================

puts "=========================================================="
puts "Floorplan Creation - Starting"
puts "=========================================================="

#===============================================================================
# 1. Floorplan Parameters
#===============================================================================

# Chip dimensions (in microns)
set die_width 15000
set die_height 15000
set core_margin 1200
set core_utilization 0.70

# Calculate core dimensions
set core_width [expr $die_width - 2 * $core_margin]
set core_height [expr $die_height - 2 * $core_margin]

puts "[INFO] Die size: ${die_width} x ${die_height} um"
puts "[INFO] Core size: ${core_width} x ${core_height} um"
puts "[INFO] Core utilization: $core_utilization"

#===============================================================================
# 2. Create Floorplan
#===============================================================================

puts "=========================================================="
puts "Creating Basic Floorplan"
puts "=========================================================="

# Create floorplan with core margins
create_floorplan \
  -core_margins_by die \
  -die_size [list $die_width $die_height $core_margin $core_margin] \
  -utilization $core_utilization \
  -aspect_ratio 1.0

puts "[INFO] Basic floorplan created"

#===============================================================================
# 3. Die Area Setup
#===============================================================================

# Set die boundary
set die_boundary [list \
  [list 0 0] \
  [list $die_width 0] \
  [list $die_width $die_height] \
  [list 0 $die_height] \
  [list 0 0] \
]

# Create die area obstruction
create_obstruction -boundary $die_boundary -layer DIEAREA

puts "[INFO] Die boundary set"

#===============================================================================
# 4. IO Ring Setup
#===============================================================================

puts "=========================================================="
puts "Configuring IO Ring"
puts "=========================================================="

# IO ring width
set io_ring_width 100

# Create IO ring obstructions
# Top IO ring
create_obstruction -boundary [list [list 0 [expr $die_height - $io_ring_width]] [list $die_width $die_height]] -layer IO_RING
# Bottom IO ring
create_obstruction -boundary [list [list 0 0] [list $die_width $io_ring_width]] -layer IO_RING
# Left IO ring
create_obstruction -boundary [list [list 0 0] [list $io_ring_width $die_height]] -layer IO_RING
# Right IO ring
create_obstruction -boundary [list [list [expr $die_width - $io_ring_width] 0] [list $die_width $die_height]] -layer IO_RING

puts "[INFO] IO ring obstructions created"

#===============================================================================
# 5. Power Domain Region Setup
#===============================================================================

puts "=========================================================="
puts "Creating Power Domain Regions"
puts "=========================================================="

# Power domain regions (coordinates in microns)
# PD_CPU: Upper left region (4x Cortex-A78AE)
set pd_cpu_origin_x 1300
set pd_cpu_origin_y 1300
set pd_cpu_width 5500
set pd_cpu_height 5500

create_power_domain \
  -name PD_CPU \
  -origin [list $pd_cpu_origin_x $pd_cpu_origin_y] \
  -size [list $pd_cpu_width $pd_cpu_height]

puts "[INFO] PD_CPU region: (${pd_cpu_origin_x}, ${pd_cpu_origin_y}) size ${pd_cpu_width}x${pd_cpu_height}"

# PD_NPU: Right region (4x NPU Cluster)
set pd_npu_origin_x 7000
set pd_npu_origin_y 1300
set pd_npu_width 5500
set pd_npu_height 10500

create_power_domain \
  -name PD_NPU \
  -origin [list $pd_npu_origin_x $pd_npu_origin_y] \
  -size [list $pd_npu_width $pd_npu_height]

puts "[INFO] PD_NPU region: (${pd_npu_origin_x}, ${pd_npu_origin_y}) size ${pd_npu_width}x${pd_npu_height}"

# PD_GPU: Lower left region (Mali-G78)
set pd_gpu_origin_x 1300
set pd_gpu_origin_y 7000
set pd_gpu_width 5500
set pd_gpu_height 4500

create_power_domain \
  -name PD_GPU \
  -origin [list $pd_gpu_origin_x $pd_gpu_origin_y] \
  -size [list $pd_gpu_width $pd_gpu_height]

puts "[INFO] PD_GPU region: (${pd_gpu_origin_x}, ${pd_gpu_origin_y}) size ${pd_gpu_width}x${pd_gpu_height}"

# PD_MEM: Bottom center (L3 Cache + DDR Controller)
set pd_mem_origin_x 7000
set pd_mem_origin_y 7000
set pd_mem_width 5500
set pd_mem_height 4500

create_power_domain \
  -name PD_MEM \
  -origin [list $pd_mem_origin_x $pd_mem_origin_y] \
  -size [list $pd_mem_width $pd_mem_height]

puts "[INFO] PD_MEM region: (${pd_mem_origin_x}, ${pd_mem_origin_y}) size ${pd_mem_width}x${pd_mem_height}"

# PD_SYS: Center region (System peripherals)
set pd_sys_origin_x 1300
set pd_sys_origin_y 7000
set pd_sys_width 5500
set pd_sys_height 4500

create_power_domain \
  -name PD_SYS \
  -origin [list $pd_sys_origin_x $pd_sys_origin_y] \
  -size [list $pd_sys_width $pd_sys_height]

puts "[INFO] PD_SYS region: (${pd_sys_origin_x}, ${pd_sys_origin_y}) size ${pd_sys_width}x${pd_sys_height}"

# PD_SAFETY: Safety island (Cortex-R52)
set pd_safety_origin_x 1300
set pd_safety_origin_y 1300
set pd_safety_width 2500
set pd_safety_height 2500

create_power_domain \
  -name PD_SAFETY \
  -origin [list $pd_safety_origin_x $pd_safety_origin_y] \
  -size [list $pd_safety_width $pd_safety_height]

puts "[INFO] PD_SAFETY region: (${pd_safety_origin_x}, ${pd_safety_origin_y}) size ${pd_safety_width}x${pd_safety_height}"

#===============================================================================
# 6. Macro Cell Placement
#===============================================================================

puts "=========================================================="
puts "Placing Macro Cells"
puts "=========================================================="

# Macro placement parameters
set macro_group_spacing 100

# CPU Cluster 0 - Cortex-A78AE x4 (Upper left)
place_macro \
  -macros [get_cells -filter "name =~ *cpu_cluster_0*"] \
  -location [list 1500 1500] \
  -orientation R0

place_macro \
  -macros [get_cells -filter "name =~ *cpu_cluster_1*"] \
  -location [list 4500 1500] \
  -orientation R0

place_macro \
  -macros [get_cells -filter "name =~ *cpu_cluster_2*"] \
  -location [list 1500 4500] \
  -orientation R0

place_macro \
  -macros [get_cells -filter "name =~ *cpu_cluster_3*"] \
  -location [list 4500 4500] \
  -orientation R0

puts "[INFO] CPU clusters placed"

# Safety CPU - Cortex-R52 (Dual lock-step)
place_macro \
  -macros [get_cells -filter "name =~ *cortex_r52*"] \
  -location [list 1500 1500] \
  -orientation R0

puts "[INFO] Safety CPU placed"

# NPU Cluster x4 (Right side)
place_macro \
  -macros [get_cells -filter "name =~ *npu_cluster_0*"] \
  -location [list 7200 1500] \
  -orientation R0

place_macro \
  -macros [get_cells -filter "name =~ *npu_cluster_1*"] \
  -location [list 7200 4200] \
  -orientation R0

place_macro \
  -macros [get_cells -filter "name =~ *npu_cluster_2*"] \
  -location [list 7200 6900] \
  -orientation R0

place_macro \
  -macros [get_cells -filter "name =~ *npu_cluster_3*"] \
  -location [list 7200 9600] \
  -orientation R0

puts "[INFO] NPU clusters placed"

# GPU - Mali-G78 (Lower left)
place_macro \
  -macros [get_cells -filter "name =~ *mali_g78*"] \
  -location [list 1500 7200] \
  -orientation R0

puts "[INFO] GPU placed"

# ISP (Image Signal Processor)
place_macro \
  -macros [get_cells -filter "name =~ *isp*"] \
  -location [list 3500 7200] \
  -orientation R0

puts "[INFO] ISP placed"

# L3 Cache (Center)
place_macro \
  -macros [get_cells -filter "name =~ *l3_cache*"] \
  -location [list 7500 7500] \
  -orientation R0

puts "[INFO] L3 Cache placed"

# DDR Controller (Near DDR PHY)
place_macro \
  -macros [get_cells -filter "name =~ *ddr_controller*"] \
  -location [list 11000 7500] \
  -orientation R0

puts "[INFO] DDR Controller placed"

# PCIe Controller (Top right corner)
place_macro \
  -macros [get_cells -filter "name =~ *pcie_controller*"] \
  -location [list 11000 1500] \
  -orientation R0

puts "[INFO] PCIe Controller placed"

# USB Controller (Bottom right corner)
place_macro \
  -macros [get_cells -filter "name =~ *usb_controller*"] \
  -location [list 11000 11000] \
  -orientation R0

puts "[INFO] USB Controller placed"

#===============================================================================
# 7. Create Placement Blockages
#===============================================================================

puts "=========================================================="
puts "Creating Placement Blockages"
puts "=========================================================="

# Block IO ring area
create_placement_blockage -boundary [list [list 0 0] [list $die_width $core_margin]] -name "io_blockage_bottom"
create_placement_blockage -boundary [list [list 0 [expr $die_height - $core_margin]] [list $die_width $die_height]] -name "io_blockage_top"
create_placement_blockage -boundary [list [list 0 0] [list $core_margin $die_height]] -name "io_blockage_left"
create_placement_blockage -boundary [list [list [expr $die_width - $core_margin] 0] [list $die_width $die_height]] -name "io_blockage_right"

# Create macro hard blockage around placed macros
foreach macro [get_macros] {
  set bbox [get_attribute $macro bounding_box]
  if {$bbox ne ""} {
    set min_x [lindex [lindex $bbox 0] 0]
    set min_y [lindex [lindex $bbox 0] 1]
    set max_x [lindex [lindex $bbox 1] 0]
    set max_y [lindex [lindex $bbox 1] 1]
    
    # Add 5um margin
    set margin 5
    set min_x [expr $min_x - $margin]
    set min_y [expr $min_y - $margin]
    set max_x [expr $max_x + $margin]
    set max_y [expr $max_y + $margin]
    
    create_placement_blockage -boundary [list [list $min_x $min_y] [list $max_x $max_y]] -name "macro_blockage_[get_object_name $macro]"
  }
}

puts "[INFO] Placement blockages created"

#===============================================================================
# 8. Power Network Creation
#===============================================================================

puts "=========================================================="
puts "Creating Power Network"
puts "=========================================================="

# Power and ground net names
set power_net "VDD"
set ground_net "VSS"

# Create power and ground nets
create_net -power $power_net
create_net -ground $ground_net

puts "[INFO] Power nets created: $power_net, $ground_net"

# Create power strap layers for TSMC 5nm
# Vertical straps on M10
create_power_straps \
  -nets [list $power_net $ground_net] \
  -layer M10 \
  -width 5.0 \
  -pitch 50.0 \
  -offset 2.5 \
  -direction vertical

# Horizontal straps on M9
create_power_straps \
  -nets [list $power_net $ground_net] \
  -layer M9 \
  -width 5.0 \
  -pitch 50.0 \
  -offset 2.5 \
  -direction horizontal

# Additional straps on M8 for better distribution
create_power_straps \
  -nets [list $power_net $ground_net] \
  -layer M8 \
  -width 3.0 \
  -pitch 40.0 \
  -offset 1.5 \
  -direction vertical

# Horizontal straps on M7
create_power_straps \
  -nets [list $power_net $ground_net] \
  -layer M7 \
  -width 3.0 \
  -pitch 40.0 \
  -offset 1.5 \
  -direction horizontal

puts "[INFO] Power straps created on M7-M10"

# Create ring at die edge
create_power_ring \
  -nets [list $power_net $ground_net] \
  -layer_start M10 \
  -layer_end M7 \
  -width 10.0 \
  -spacing 2.0

puts "[INFO] Power ring created"

#===============================================================================
# 9. IO Ring Power
#===============================================================================

# Create IO power rings
create_power_straps \
  -nets [list $power_net $ground_net] \
  -layer M6 \
  -width 2.0 \
  -pitch 20.0 \
  -offset 1.0 \
  -follow_io

puts "[INFO] IO power straps created"

#===============================================================================
# 10. Add Standard Cell Power Rails
#===============================================================================

# Enable standard cell power rails
set_sc_ppms_options \
  -power_net $power_net \
  -ground_net $ground_net \
  -power_pin VDD \
  -ground_pin VSS

puts "[INFO] Standard cell power rails configured"

#===============================================================================
# 11. Floorplan Report
#===============================================================================

puts "=========================================================="
puts "Floorplan Report"
puts "=========================================================="

# Report floorplan
report_floorplan

# Report macros
puts "[INFO] Placed macros:"
foreach macro [get_macros] {
  set name [get_object_name $macro]
  set bbox [get_attribute $macro bounding_box]
  puts "  - $name: $bbox"
}

# Report placement blockages
set blockages [get_placement_blockages]
puts "[INFO] Placement blockages: [sizeof $blockages]"

# Report power network
puts "[INFO] Power network summary:"
report_power_grid

puts "[INFO] Floorplan creation completed successfully"
puts "=========================================================="
