# YaoGuang SoC DFT Configuration
# Version: V1.0
# Date: 2026-01-18
# Description: Complete DFT configuration for YaoGuang automotive SoC

#===============================================================================
# 1. DFT MODE SETTINGS
#===============================================================================

# Enable scan mode
set_dft_mode -scan

# Enable compression for test data reduction
set_dft_mode -compression

# Enable boundary scan
set_dft_mode -boundary_scan

#===============================================================================
# 2. SCAN CHAIN CONFIGURATION
#===============================================================================

# Overall scan configuration
set_scan_configuration \
    -chain_count 16 \
    -max_chain_length 312500 \
    -min_chain_length 50000 \
    -compression_enable true \
    -compression_ratio 10 \
    -scan_style multiplexed_flip_flop \
    -replace_scanned_cells true \
    -preserve_drivers true \
    -scan_in_pin SI \
    -scan_out_pin SO

# Chain balancing target (max imbalance percentage)
set_scan_configuration -balance_chains true
set_scan_configuration -max_chain_imbalance 10

#===============================================================================
# 3. SCAN CHAIN DEFINITIONS
#===============================================================================

# CPU Domain (4 Cortex-A78AE cores, 4 chains)
define_scan_chain -name CHAIN_CPU0 \
    -scan_in SI_CPU0 -scan_out SO_CPU0 \
    -scan_clock SCLK_CPU \
    -elements [get_cells -hierarchical *cpu0*reg*]

define_scan_chain -name CHAIN_CPU1 \
    -scan_in SI_CPU1 -scan_out SO_CPU1 \
    -scan_clock SCLK_CPU \
    -elements [get_cells -hierarchical *cpu1*reg*]

define_scan_chain -name CHAIN_CPU2 \
    -scan_in SI_CPU2 -scan_out SO_CPU2 \
    -scan_clock SCLK_CPU \
    -elements [get_cells -hierarchical *cpu2*reg*]

define_scan_chain -name CHAIN_CPU3 \
    -scan_in SI_CPU3 -scan_out SO_CPU3 \
    -scan_clock SCLK_CPU \
    -elements [get_cells -hierarchical *cpu3*reg*]

# Safety Island (2 Cortex-R52 cores, 2 chains)
define_scan_chain -name CHAIN_SAFETY0 \
    -scan_in SI_SAFETY0 -scan_out SO_SAFETY0 \
    -scan_clock SCLK_SAFETY \
    -elements [get_cells -hierarchical *safety0*reg*]

define_scan_chain -name CHAIN_SAFETY1 \
    -scan_in SI_SAFETY1 -scan_out SO_SAFETY1 \
    -scan_clock SCLK_SAFETY \
    -elements [get_cells -hierarchical *safety1*reg*]

# NPU Domain (4 clusters, 4 chains)
define_scan_chain -name CHAIN_NPU0 \
    -scan_in SI_NPU0 -scan_out SO_NPU0 \
    -scan_clock SCLK_NPU \
    -elements [get_cells -hierarchical *npu0*reg*]

define_scan_chain -name CHAIN_NPU1 \
    -scan_in SI_NPU1 -scan_out SO_NPU1 \
    -scan_clock SCLK_NPU \
    -elements [get_cells -hierarchical *npu1*reg*]

define_scan_chain -name CHAIN_NPU2 \
    -scan_in SI_NPU2 -scan_out SO_NPU2 \
    -scan_clock SCLK_NPU \
    -elements [get_cells -hierarchical *npu2*reg*]

define_scan_chain -name CHAIN_NPU3 \
    -scan_in SI_NPU3 -scan_out SO_NPU3 \
    -scan_clock SCLK_NPU \
    -elements [get_cells -hierarchical *npu3*reg*]

# GPU Domain (1 Mali-G78, 2 chains)
define_scan_chain -name CHAIN_GPU0 \
    -scan_in SI_GPU0 -scan_out SO_GPU0 \
    -scan_clock SCLK_GPU \
    -elements [get_cells -hierarchical *gpu0*reg*]

define_scan_chain -name CHAIN_GPU1 \
    -scan_in SI_GPU1 -scan_out SO_GPU1 \
    -scan_clock SCLK_GPU \
    -elements [get_cells -hierarchical *gpu1*reg*]

# NoC (1 chain)
define_scan_chain -name CHAIN_NOC \
    -scan_in SI_NOC -scan_out SO_NOC \
    -scan_clock SCLK_SYS \
    -elements [get_cells -hierarchical *noc*reg*]

# Memory Controllers (1 chain)
define_scan_chain -name CHAIN_MEM \
    -scan_in SI_MEM -scan_out SO_MEM \
    -scan_clock SCLK_MEM \
    -elements [get_cells -hierarchical *mem*reg*]

# Peripherals (2 chains)
define_scan_chain -name CHAIN_PERI0 \
    -scan_in SI_PERI0 -scan_out SO_PERI0 \
    -scan_clock SCLK_APB \
    -elements [get_cells -hierarchical *peri0*reg*]

define_scan_chain -name CHAIN_PERI1 \
    -scan_in SI_PERI1 -scan_out SO_PERI1 \
    -scan_clock SCLK_APB \
    -elements [get_cells -hierarchical *peri1*reg*]

#===============================================================================
# 4. CLOCK CONFIGURATION FOR DFT
#===============================================================================

# Define scan clocks
set_dft_clock -names {SCLK_CPU SCLK_NPU SCLK_GPU SCLK_SYS SCLK_SAFETY SCLK_MEM SCLK_APB} \
    -source {core_clk npu_clk gpu_clk sys_clk safety_clk mem_clk apb_clk}

# Test clock constraints
set_test_clock SCLK_CPU -period 2.5
set_test_clock SCLK_NPU -period 2.5
set_test_clock SCLK_GPU -period 5.0
set_test_clock SCLK_SYS -period 10.0
set_test_clock SCLK_SAFETY -period 2.5
set_test_clock SCLK_MEM -period 5.0
set_test_clock SCLK_APB -period 10.0

#===============================================================================
# 5. TEST MODE SETTINGS
#===============================================================================

# DFT mode settings
set_dft_mode -test

# Set test mode pin mappings
set_dft_port SE -test_mode scan
set_dft_port SE_SCAN -test_mode scan
set_dft_port SE_BIST -test_mode bist
set_dft_port SE_MBIST -test_mode mbist

#===============================================================================
# 6. MBIST CONFIGURATION
#===============================================================================

# Create MBIST configuration
create_mbist_configuration \
    -output yaoguang_mbist.tcl \
    -algorithm {march_c+ march_ss checkerboard}

# MBIST controller placement (auto)
set_mbist_configuration -place_controllers auto

# MBIST wrapper insertion
insert_mbist_wrappers -all

#===============================================================================
# 7. ATPG CONFIGURATION
#===============================================================================

# ATPG settings
set_atpg_configuration \
    -max_patterns 50000 \
    -pattern_type {stuck_at transition} \
    -compression on \
    -drf_mode balanced

# Fault model settings
set_atpg_configuration -fault_type stuck_at,transition,path_delay

# Coverage targets
set_atpg_configuration \
    -target_fault_coverage 99.0 \
    -target_test_coverage 99.0

#===============================================================================
# 8. BOUNDARY SCAN CONFIGURATION
#===============================================================================

# Boundary scan settings
set_boundary_scan -standard IEEE_1149.1

# TAP controller configuration
set_boundary_scan -tap_controller yaoguang_tap

# Boundary scan cell insertion
insert_boundary_scan

#===============================================================================
# 9. JTAG CONFIGURATION
#===============================================================================

# JTAG settings
set_jtag -standard IEEE_1149.1
set_jtag -instruction_length 8
set_jtag -register_length 32

# JTAG instructions
set_jtag_instruction IDCODE   -opcode 0b00000010
set_jtag_instruction BYPASS   -opcode 0b11111111
set_jtag_instruction SAMPLE   -opcode 0b00000001
set_jtag_instruction PRELOAD  -opcode 0b00000001
set_jtag_instruction EXTEST   -opcode 0b00000000
set_jtag_instruction INTEST   -opcode 0b00000111
set_jtag_instruction SCAN_N   -opcode 0b00100100
set_jtag_instruction CLAMP    -opcode 0b00111010
set_jtag_instruction HIGHZ    -opcode 0b00111111
set_jtag_instruction MBIST    -opcode 0b00101000
set_jtag_instruction LBIST    -opcode 0b00101001

#===============================================================================
# 10. TEST POINT INSERTION
#===============================================================================

# Test point settings
set_test_point -control_points auto
set_test_point -observe_points auto

#===============================================================================
# 11. DFT SIGNALS
#===============================================================================

# Define DFT signal constraints
set_dft_signal -type ScanEnable -port SE
set_dft_signal -type TestModeSelect -port TMS
set_dft_signal -type TestDataIn -port TDI
set_dft_signal -type TestDataOut -port TDO
set_dft_signal -type TestClock -port TCK

#===============================================================================
# 12. REPORT SETTINGS
#===============================================================================

# Enable comprehensive reporting
set_dft_report -verbose true
set_dft_report -show_all_chains true

#===============================================================================
# END OF DFT CONFIGURATION
#===============================================================================

puts "\[DFT_CONFIG\] DFT configuration loaded successfully"
puts "\[DFT_CONFIG\] Scan chains: 16"
puts "\[DFT_CONFIG\] Compression ratio: 10x"
puts "\[DFT_CONFIG\] Target coverage: > 99%"
