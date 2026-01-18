#!/usr/bin/env tclsh
#===============================================================================
# YaoGuang SoC DFT Insertion Script
# Version: V1.0
# Date: 2026-01-18
#===============================================================================

#===============================================================================
# 1. SETUP AND INITIALIZATION
#===============================================================================

puts "========================================"
puts "  YaoGuang SoC DFT Insertion"
puts "========================================"
puts "Date: [clock format [clock seconds]]"
puts ""

# Record start time
set start_time [clock seconds]

#===============================================================================
# 2. READ DESIGN
#===============================================================================

puts "========================================"
puts "  Step 1: Reading Design"
puts "========================================"

# Check if netlist exists
if { ![file exists yaoguang_soc_netlist.v] } {
    puts "\[ERROR\] Synthesis netlist not found: yaoguang_soc_netlist.v"
    puts "\[ERROR\] Please run synthesis first"
    exit 1
}

# Read synthesized netlist
read_verilog yaoguang_soc_netlist.v
puts "\[INFO\] Design netlist loaded"

#===============================================================================
# 3. LOAD DFT CONFIGURATION
#===============================================================================

puts ""
puts "========================================"
puts "  Step 2: Loading DFT Configuration"
puts "========================================"

# Source DFT configuration
source dft_config.tcl
puts "\[INFO\] DFT configuration loaded"

#===============================================================================
# 4. CREATE TEST PROTOCOL
#===============================================================================

puts ""
puts "========================================"
puts "  Step 3: Creating Test Protocol"
puts "========================================"

# Create test protocol with async reset inference
create_test_protocol -infer_asynch
puts "\[INFO\] Test protocol created"

#===============================================================================
# 5. SCAN CHAIN CONFIGURATION
#===============================================================================

puts ""
puts "========================================"
puts "  Step 4: Configuring Scan Chains"
puts "========================================"

# Set scan configuration
set_scan_configuration \
    -chain_count 16 \
    -compression_ratio 10 \
    -scan_style multiplexed_flip_flop \
    -replace_scanned_cells true

puts "\[INFO\] Scan chains configured"

#===============================================================================
# 6. INSERT DFT
#===============================================================================

puts ""
puts "========================================"
puts "  Step 5: Inserting DFT"
puts "========================================"

# Insert all DFT (scan, boundary scan, MBIST)
insert_dft

puts "\[INFO\] DFT insertion complete"

#===============================================================================
# 7. VERIFY SCAN CHAINS
#===============================================================================

puts ""
puts "========================================"
puts "  Step 6: Verifying Scan Chains"
puts "========================================"

# Report scan chain statistics
report_scan_chains

# Check scan chain continuity
set scan_issues [check_scan_chains]
if { $scan_issues > 0 } {
    puts "\[WARNING\] Scan chain issues found: $scan_issues"
} else {
    puts "\[INFO\] Scan chain continuity verified"
}

#===============================================================================
# 8. DFT VALIDATION
#===============================================================================

puts ""
puts "========================================"
puts "  Step 7: DFT Validation"
puts "========================================"

# Check for design rule violations
check_dft_rules -verbose

puts "\[INFO\] DFT validation complete"

#===============================================================================
# 9. GENERATE REPORTS
#===============================================================================

puts ""
puts "========================================"
puts "  Step 8: Generating Reports"
puts "========================================"

# Create reports directory
file mkdir reports

# DFT summary report
redirect reports/dft_summary.rpt {
    report_dft -summary
}

# Scan chain details
redirect reports/scan_chains.rpt {
    report_scan_chains -verbose
}

# MBIST report
redirect reports/mbist.rpt {
    report_mbist
}

# Boundary scan report
redirect reports/boundary_scan.rpt {
    report_boundary_scan
}

# Test coverage estimate
redirect reports/test_coverage.rpt {
    report_test_coverage
}

puts "\[INFO\] Reports generated"

#===============================================================================
# 10. SAVE OUTPUTS
#===============================================================================

puts ""
puts "========================================"
puts "  Step 9: Saving Outputs"
puts "========================================"

# Create output directory
file mkdir output

# Save DFT netlist
write -format verilog -hierarchy -output output/yaoguang_soc_dft.v
puts "\[INFO\] DFT netlist saved: output/yaoguang_soc_dft.v"

# Save test protocol
write_test_protocol -output output/yaoguang_soc.tpf
puts "\[INFO\] Test protocol saved: output/yaoguang_soc.tpf"

# Save DFT database
write -format ddc -output output/yaoguang_soc_dft.ddc
puts "\[INFO\] DFT database saved: output/yaoguang_soc_dft.ddc"

# Save ATPG setup
redirect output/atpg_setup.tcl {
    report_atpg_configuration
}

puts "\[INFO\] All outputs saved"

#===============================================================================
# 11. SUMMARY
#===============================================================================

# Calculate duration
set end_time [clock seconds]
set duration [expr {$end_time - $start_time}]

puts ""
puts "========================================"
puts "  DFT Insertion Complete"
puts "========================================"
puts "Duration: $duration seconds"
puts ""
puts "Outputs:"
puts "  - Netlist: output/yaoguang_soc_dft.v"
puts "  - Test Protocol: output/yaoguang_soc.tpf"
puts "  - Database: output/yaoguang_soc_dft.ddc"
puts ""
puts "Reports:"
puts "  - reports/dft_summary.rpt"
puts "  - reports/scan_chains.rpt"
puts "  - reports/mbist.rpt"
puts "  - reports/boundary_scan.rpt"
puts "  - reports/test_coverage.rpt"
puts "========================================"

#===============================================================================
# END OF DFT INSERTION
#===============================================================================
