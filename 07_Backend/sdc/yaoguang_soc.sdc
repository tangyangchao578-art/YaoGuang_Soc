#############################################################################
# YaoGuang SoC Timing Constraints File
# Version: 1.0
# Date: 2026-01-18
# Author: Backend Engineering Team
# Description: Complete SDC for YaoGuang automotive SoC
#############################################################################

#############################################################################
# 1. VERSION AND UNIT SETTINGS
#############################################################################
set sdc_version 2.1
set_units -time ns -resistance kohm -capacitance pF -voltage V -current mA

#############################################################################
# 2. CREATE PRIMARY CLOCKS
#############################################################################

# CPU Core Clock - 2.0 GHz
create_clock -name clk_core -period 0.5 [get_ports clk_core]
set_clock_latency -source -max 0.15 [get_clocks clk_core]
set_clock_latency -source -min 0.05 [get_clocks clk_core]
set_clock_uncertainty -setup 0.05 [get_clocks clk_core]
set_clock_uncertainty -hold 0.02 [get_clocks clk_core]

# NPU Neural Processor Clock - 2.0 GHz
create_clock -name clk_npu -period 0.5 [get_ports clk_npu]
set_clock_latency -source -max 0.15 [get_clocks clk_npu]
set_clock_latency -source -min 0.05 [get_clocks clk_npu]
set_clock_uncertainty -setup 0.05 [get_clocks clk_npu]
set_clock_uncertainty -hold 0.02 [get_clocks clk_npu]

# GPU Clock - 1.0 GHz
create_clock -name clk_gpu -period 1.0 [get_ports clk_gpu]
set_clock_latency -source -max 0.12 [get_clocks clk_gpu]
set_clock_latency -source -min 0.04 [get_clocks clk_gpu]
set_clock_uncertainty -setup 0.04 [get_clocks clk_gpu]
set_clock_uncertainty -hold 0.015 [get_clocks clk_gpu]

# System Bus/NoC Clock - 500 MHz
create_clock -name clk_sys -period 2.0 [get_ports clk_sys]
set_clock_latency -source -max 0.2 [get_clocks clk_sys]
set_clock_latency -source -min 0.08 [get_clocks clk_sys]
set_clock_uncertainty -setup 0.03 [get_clocks clk_sys]
set_clock_uncertainty -hold 0.01 [get_clocks clk_sys]

# Memory Controller Clock - 800 MHz
create_clock -name clk_mem -period 1.25 [get_ports clk_mem]
set_clock_latency -source -max 0.12 [get_clocks clk_mem]
set_clock_latency -source -min 0.05 [get_clocks clk_mem]
set_clock_uncertainty -setup 0.04 [get_clocks clk_mem]
set_clock_uncertainty -hold 0.015 [get_clocks clk_mem]

# ISP Clock - 600 MHz
create_clock -name clk_isp -period 1.67 [get_ports clk_isp]
set_clock_latency -source -max 0.15 [get_clocks clk_isp]
set_clock_latency -source -min 0.06 [get_clocks clk_isp]
set_clock_uncertainty -setup 0.035 [get_clocks clk_isp]
set_clock_uncertainty -hold 0.012 [get_clocks clk_isp]

# Display Clock - 300 MHz
create_clock -name clk_display -period 3.33 [get_ports clk_display]
set_clock_latency -source -max 0.2 [get_clocks clk_display]
set_clock_latency -source -min 0.08 [get_clocks clk_display]
set_clock_uncertainty -setup 0.03 [get_clocks clk_display]
set_clock_uncertainty -hold 0.01 [get_clocks clk_display]

# PCIe Clock - 250 MHz
create_clock -name clk_pcie -period 4.0 [get_ports clk_pcie_ref]
set_clock_latency -source -max 0.1 [get_clocks clk_pcie]
set_clock_latency -source -min 0.04 [get_clocks clk_pcie]
set_clock_uncertainty -setup 0.05 [get_clocks clk_pcie]
set_clock_uncertainty -hold 0.02 [get_clocks clk_pcie]

# Ethernet Clock - 250 MHz
create_clock -name clk_eth -period 4.0 [get_ports clk_eth_ref]
set_clock_latency -source -max 0.1 [get_clocks clk_eth]
set_clock_latency -source -min 0.04 [get_clocks clk_eth]
set_clock_uncertainty -setup 0.05 [get_clocks clk_eth]
set_clock_uncertainty -hold 0.02 [get_clocks clk_eth]

# USB Clock - 250 MHz
create_clock -name clk_usb -period 4.0 [get_ports clk_usb_ref]
set_clock_latency -source -max 0.1 [get_clocks clk_usb]
set_clock_latency -source -min 0.04 [get_clocks clk_usb]
set_clock_uncertainty -setup 0.05 [get_clocks clk_usb]
set_clock_uncertainty -hold 0.02 [get_clocks clk_usb]

# Audio Clock - 100 MHz
create_clock -name clk_audio -period 10.0 [get_ports clk_audio]
set_clock_latency -source -max 0.3 [get_clocks clk_audio]
set_clock_latency -source -min 0.1 [get_clocks clk_audio]
set_clock_uncertainty -setup 0.025 [get_clocks clk_audio]
set_clock_uncertainty -hold 0.008 [get_clocks clk_audio]

# APB Peripheral Bus Clock - 100 MHz
create_clock -name clk_apb -period 10.0 [get_ports clk_apb]
set_clock_latency -source -max 0.3 [get_clocks clk_apb]
set_clock_latency -source -min 0.1 [get_clocks clk_apb]
set_clock_uncertainty -setup 0.025 [get_clocks clk_apb]
set_clock_uncertainty -hold 0.008 [get_clocks clk_apb]

# RTC Clock - 32.768 kHz
create_clock -name clk_rtc -period 30.52us [get_ports clk_rtc]
set_clock_latency -source -max 1.0 [get_clocks clk_rtc]
set_clock_latency -source -min 0.5 [get_clocks clk_rtc]
set_clock_uncertainty -setup 0.5 [get_clocks clk_rtc]
set_clock_uncertainty -hold 0.2 [get_clocks clk_rtc]

#############################################################################
# 3. GENERATED CLOCKS
#############################################################################

# Core Clock Dividers
create_generated_clock -name clk_core_div2 \
    -source [get_pins u_clkgen/clk_core_out] \
    -divide_by 2 [get_pins u_clkgen/div2_core_reg/Q]

create_generated_clock -name clk_core_div4 \
    -source [get_pins u_clkgen/clk_core_out] \
    -divide_by 4 [get_pins u_clkgen/div4_core_reg/Q]

# NPU Clock Dividers
create_generated_clock -name clk_npu_div2 \
    -source [get_pins u_clkgen/clk_npu_out] \
    -divide_by 2 [get_pins u_clkgen/div2_npu_reg/Q]

create_generated_clock -name clk_npu_div4 \
    -source [get_pins u_clkgen/clk_npu_out] \
    -divide_by 4 [get_pins u_clkgen/div4_npu_reg/Q]

# GPU Clock Divider
create_generated_clock -name clk_gpu_div2 \
    -source [get_pins u_clkgen/clk_gpu_out] \
    -divide_by 2 [get_pins u_clkgen/div2_gpu_reg/Q]

# DDR DQS Clocks (Data Strobe)
create_generated_clock -name ddr_dqs0 \
    -source [get_pins u_ddr_ctrl/ddr_clk] \
    -divide_by 2 [get_ports DDR_DQS0_P]

create_generated_clock -name ddr_dqs1 \
    -source [get_pins u_ddr_ctrl/ddr_clk] \
    -divide_by 2 [get_ports DDR_DQS1_P]

create_generated_clock -name ddr_dqs2 \
    -source [get_pins u_ddr_ctrl/ddr_clk] \
    -divide_by 2 [get_ports DDR_DQS2_P]

create_generated_clock -name ddr_dqs3 \
    -source [get_pins u_ddr_ctrl/ddr_clk] \
    -divide_by 2 [get_ports DDR_DQS3_P]

# PCIe Reference Clock (generated from external 100MHz)
create_generated_clock -name pcie_ref_clk \
    -source [get_ports clk_pcie_ref] \
    -multiply_by 1 [get_pins u_pcie_ctrl/ref_clk_buf/O]

# Ethernet Reference Clock
create_generated_clock -name eth_rx_clk \
    -source [get_ports eth_ref_clk] \
    -multiply_by 1 [get_pins u_eth_mac/rx_clk_buf/O]

create_generated_clock -name eth_tx_clk \
    -source [get_ports eth_ref_clk] \
    -multiply_by 1 [get_pins u_eth_mac/tx_clk_buf/O]

# USB Reference Clock
create_generated_clock -name usb_ref_clk \
    -source [get_ports clk_usb_ref] \
    -multiply_by 1 [get_pins u_usb_ctrl/ref_clk_buf/O]

#############################################################################
# 4. CLOCK GROUPS
#############################################################################

# Synchronous Clock Groups (Same Source Domain)
create_clock_group -group clk_core -group clk_core_div2 -group clk_core_div4 \
    -name clk_core_group -physically_exclusive

create_clock_group -group clk_npu -group clk_npu_div2 -group clk_npu_div4 \
    -name clk_npu_group -physically_exclusive

create_clock_group -group clk_gpu -group clk_gpu_div2 \
    -name clk_gpu_group -physically_exclusive

# Related Core and NPU Clocks (Same PLL Source)
create_clock_group -group clk_core -group clk_npu \
    -name core_npu_sync -asynchronous

# Asynchronous Clock Groups
create_clock_group -group clk_sys -group clk_pcie -group clk_eth \
    -group clk_usb -name async_sys_periph -asynchronous

create_clock_group -group clk_sys -group clk_display \
    -name async_sys_display -asynchronous

create_clock_group -group clk_sys -group clk_isp \
    -name async_sys_isp -asynchronous

create_clock_group -group clk_sys -group clk_mem \
    -name async_sys_mem -asynchronous

create_clock_group -group clk_pcie -group clk_eth \
    -group clk_usb -name async_pcie_eth_usb -asynchronous

create_clock_group -group clk_audio -group clk_apb \
    -group clk_rtc -name async_slow_clocks -asynchronous

#############################################################################
# 5. CLOCK LATENCY AND UNCERTAINTY
#############################################################################

# Network Latency (post-layout estimated)
set_clock_latency -max 0.08 [get_clocks clk_core]
set_clock_latency -min 0.02 [get_clocks clk_core]

set_clock_latency -max 0.08 [get_clocks clk_npu]
set_clock_latency -min 0.02 [get_clocks clk_npu]

set_clock_latency -max 0.06 [get_clocks clk_sys]
set_clock_latency -min 0.02 [get_clocks clk_sys]

# Additional Uncertainty for Inter-clock Domain
set_clock_uncertainty -from [get_clocks clk_core] -to [get_clocks clk_npu] 0.08
set_clock_uncertainty -from [get_clocks clk_npu] -to [get_clocks clk_core] 0.08

set_clock_uncertainty -from [get_clocks clk_sys] -to [get_clocks clk_mem] 0.06
set_clock_uncertainty -from [get_clocks clk_mem] -to [get_clocks clk_sys] 0.06

#############################################################################
# 6. INPUT DELAY CONSTRAINTS
#############################################################################

# DDR5/LPDDR5 Input Delays (6400 MT/s, 800MHz DQS)
# Data valid window: 0.625ns (tRPRE + tPST)
set_input_delay -clock ddr_dqs0 -max 0.3 [get_ports DDR_DQ0*]
set_input_delay -clock ddr_dqs0 -min 0.1 [get_ports DDR_DQ0*]
set_input_delay -clock ddr_dqs1 -max 0.3 [get_ports DDR_DQ1*]
set_input_delay -clock ddr_dqs1 -min 0.1 [get_ports DDR_DQ1*]
set_input_delay -clock ddr_dqs2 -max 0.3 [get_ports DDR_DQ2*]
set_input_delay -clock ddr_dqs2 -min 0.1 [get_ports DDR_DQ2*]
set_input_delay -clock ddr_dqs3 -max 0.3 [get_ports DDR_DQ3*]
set_input_delay -clock ddr_dqs3 -min 0.1 [get_ports DDR_DQ3*]

# DDR Command/Address Inputs
set_input_delay -clock clk_mem -max 0.5 [get_ports DDR_A*]
set_input_delay -clock clk_mem -min 0.2 [get_ports DDR_A*]
set_input_delay -clock clk_mem -max 0.5 [get_ports DDR_BA*]
set_input_delay -clock clk_mem -min 0.2 [get_ports DDR_BA*]
set_input_delay -clock clk_mem -max 0.5 [get_ports DDR_CKE*]
set_input_delay -clock clk_mem -min 0.2 [get_ports DDR_CKE*]
set_input_delay -clock clk_mem -max 0.5 [get_ports DDR_CS*]
set_input_delay -clock clk_mem -min 0.2 [get_ports DDR_CS*]
set_input_delay -clock clk_mem -max 0.5 [get_ports DDR_CAS*]
set_input_delay -clock clk_mem -min 0.2 [get_ports DDR_CAS*]
set_input_delay -clock clk_mem -max 0.5 [get_ports DDR_RAS*]
set_input_delay -clock clk_mem -min 0.2 [get_ports DDR_RAS*]
set_input_delay -clock clk_mem -max 0.5 [get_ports DDR_WE*]
set_input_delay -clock clk_mem -min 0.2 [get_ports DDR_WE*]

# PCIe Input Delays (16 GT/s, 8 GT/s per lane)
# Reference clock jitter budget
set_input_delay -clock clk_pcie -max 0.1 [get_ports PCIE_RX_P*]
set_input_delay -clock clk_pcie -min 0.0 [get_ports PCIE_RX_P*]

# Ethernet 10G Input Delays (10.3125 Gbps)
set_input_delay -clock eth_rx_clk -max 0.3 [get_ports ETH_RX_P*]
set_input_delay -clock eth_rx_clk -min 0.1 [get_ports ETH_RX_P*]

# USB 3.2 Input Delays
set_input_delay -clock usb_ref_clk -max 0.2 [get_ports USB_RX_P*]
set_input_delay -clock usb_ref_clk -min 0.05 [get_ports USB_RX_P*]

# System/General Purpose Inputs
set_input_delay -clock clk_sys -max 0.8 [get_ports SYS_IN*]
set_input_delay -clock clk_sys -min 0.3 [get_ports SYS_IN*]

set_input_delay -clock clk_apb -max 1.5 [get_ports APB_IN*]
set_input_delay -clock clk_apb -min 0.5 [get_ports APB_IN*]

#############################################################################
# 7. OUTPUT DELAY CONSTRAINTS
#############################################################################

# DDR5/LPDDR5 Output Delays (6400 MT/s)
set_output_delay -clock ddr_dqs0 -max 0.3 [get_ports DDR_DQ0*]
set_output_delay -clock ddr_dqs0 -min -0.1 [get_ports DDR_DQ0*]
set_output_delay -clock ddr_dqs1 -max 0.3 [get_ports DDR_DQ1*]
set_output_delay -clock ddr_dqs1 -min -0.1 [get_ports DDR_DQ1*]
set_output_delay -clock ddr_dqs2 -max 0.3 [get_ports DDR_DQ2*]
set_output_delay -clock ddr_dqs2 -min -0.1 [get_ports DDR_DQ2*]
set_output_delay -clock ddr_dqs3 -max 0.3 [get_ports DDR_DQ3*]
set_output_delay -clock ddr_dqs3 -min -0.1 [get_ports DDR_DQ3*]

# DDR Command/Address Outputs
set_output_delay -clock clk_mem -max 0.4 [get_ports DDR_A*]
set_output_delay -clock clk_mem -min -0.2 [get_ports DDR_A*]
set_output_delay -clock clk_mem -max 0.4 [get_ports DDR_BA*]
set_output_delay -clock clk_mem -min -0.2 [get_ports DDR_BA*]
set_output_delay -clock clk_mem -max 0.4 [get_ports DDR_CKE*]
set_output_delay -clock clk_mem -min -0.2 [get_ports DDR_CKE*]
set_output_delay -clock clk_mem -max 0.4 [get_ports DDR_CS*]
set_output_delay -clock clk_mem -min -0.2 [get_ports DDR_CS*]
set_output_delay -clock clk_mem -max 0.4 [get_ports DDR_CAS*]
set_output_delay -clock clk_mem -min -0.2 [get_ports DDR_CAS*]
set_output_delay -clock clk_mem -max 0.4 [get_ports DDR_RAS*]
set_output_delay -clock clk_mem -min -0.2 [get_ports DDR_RAS*]
set_output_delay -clock clk_mem -max 0.4 [get_ports DDR_WE*]
set_output_delay -clock clk_mem -min -0.2 [get_ports DDR_WE*]

# PCIe Output Delays
set_output_delay -clock clk_pcie -max 0.1 [get_ports PCIE_TX_P*]
set_output_delay -clock clk_pcie -min -0.1 [get_ports PCIE_TX_P*]

# Ethernet 10G Output Delays
set_output_delay -clock eth_tx_clk -max 0.3 [get_ports ETH_TX_P*]
set_output_delay -clock eth_tx_clk -min -0.1 [get_ports ETH_TX_P*]

# USB 3.2 Output Delays
set_output_delay -clock usb_ref_clk -max 0.2 [get_ports USB_TX_P*]
set_output_delay -clock usb_ref_clk -min -0.1 [get_ports USB_TX_P*]

# System/General Purpose Outputs
set_output_delay -clock clk_sys -max 0.8 [get_ports SYS_OUT*]
set_output_delay -clock clk_sys -min -0.3 [get_ports SYS_OUT*]

set_output_delay -clock clk_apb -max 1.5 [get_ports APB_OUT*]
set_output_delay -clock clk_apb -min -0.5 [get_ports APB_OUT*]

#############################################################################
# 8. MULTI-CYCLE PATHS
#############################################################################

# DDR Read/Write Paths
set_multicycle_path -setup -from [get_clocks ddr_dqs*] -to [get_clocks clk_mem] 2
set_multicycle_path -hold -from [get_clocks ddr_dqs*] -to [get_clocks clk_mem] 1

set_multicycle_path -setup -from [get_clocks clk_mem] -to [get_clocks ddr_dqs*] 2
set_multicycle_path -hold -from [get_clocks clk_mem] -to [get_clocks ddr_dqs*] 1

# Async FIFO Cross Domains
set_multicycle_path -setup -from [get_clocks clk_core] -to [get_clocks clk_sys] 2
set_multicycle_path -hold -from [get_clocks clk_core] -to [get_clocks clk_sys] 1

set_multicycle_path -setup -from [get_clocks clk_npu] -to [get_clocks clk_sys] 2
set_multicycle_path -hold -from [get_clocks clk_npu] -to [get_clocks clk_sys] 1

set_multicycle_path -setup -from [get_clocks clk_gpu] -to [get_clocks clk_sys] 2
set_multicycle_path -hold -from [get_clocks clk_gpu] -to [get_clocks clk_sys] 1

# Memory Controller to/from CPU
set_multicycle_path -setup -from [get_clocks clk_mem] -to [get_clocks clk_core] 3
set_multicycle_path -hold -from [get_clocks clk_mem] -to [get_clocks clk_core] 2

set_multicycle_path -setup -from [get_clocks clk_core] -to [get_clocks clk_mem] 2
set_multicycle_path -hold -from [get_clocks clk_core] -to [get_clocks clk_mem] 1

# Display Refresh Paths (lower frequency)
set_multicycle_path -setup -from [get_clocks clk_isp] -to [get_clocks clk_display] 3
set_multicycle_path -hold -from [get_clocks clk_isp] -to [get_clocks clk_display] 2

#############################################################################
# 9. FALSE PATHS
#############################################################################

# Test Mode Paths
set_false_path -through [get_pins u_scan_chain*]
set_false_path -through [get_pins u_bist*]

# JTAG Debug Interface
set_false_path -through [get_pins u_jtag*]
set_false_path -from [get_ports JTAG_*] -to [get_clocks *]
set_false_path -from [get_clocks *] -to [get_ports JTAG_*]

# ARM Debug Interface (DAP)
set_false_path -through [get_pins u_debug_apb*]
set_false_path -from [get_ports DBG_*] -to [get_clocks *]
set_false_path -from [get_clocks *] -to [get_ports DBG_*]

# Memory BIST Paths
set_false_path -through [get_pins u_mem_bist*]

# PLL Configuration (static configuration)
set_false_path -from [get_pins u_pll_ctrl*] -to [get_clocks *]
set_false_path -from [get_clocks *] -to [get_pins u_pll_ctrl*]

# Clock Gating Configuration
set_false_path -through [get_pins u_clk_gate*_ctrl*]

# Reset Synchronizer Paths (asynchronous)
set_false_path -through [get_pins u_rst_sync*]

# Power Management Control
set_false_path -through [get_pins u_pwr_ctrl*]
set_false_path -from [get_pins u_pwr_ctrl*] -to [get_clocks *]

# Temperature Sensor Interface
set_false_path -through [get_pins u_temp_sensor*]

# Voltage Monitor Interface
set_false_path -through [get_pins u_vmon*]

# ROM Boot Memory (read-only, slow access)
set_false_path -from [get_clocks clk_rtc] -to [get_clocks clk_core]

# RTC to System Clock Domain
set_false_path -from [get_clocks clk_rtc] -to [get_clocks *]

# Test Clock Inputs
set_false_path -from [get_ports test_clk*]
set_false_path -to [get_ports test_clk*]

#############################################################################
# 10. MAX CAPACITANCE AND TRANSITION
#############################################################################

# Global Max Capacitance
set_max_capacitance 2.0 [get_design *]

# Clock Network Max Capacitance
set_max_capacitance 0.5 [get_clocks clk_core]
set_max_capacitance 0.5 [get_clocks clk_npu]
set_max_capacitance 0.3 [get_clocks clk_sys]
set_max_capacitance 0.4 [get_clocks clk_mem]

# Global Max Transition
set_max_transition 0.2 [get_design *]

# Clock Network Max Transition
set_max_transition 0.1 [get_clocks *]

# IO Max Transition
set_max_transition 0.5 [get_ports *]

#############################################################################
# 11. DRIVE STRENGTH SETTINGS
#############################################################################

# Input Drive Strength (for input ports)
set_input_transition -max 0.3 [get_ports DDR_DQ*]
set_input_transition -min 0.1 [get_ports DDR_DQ*]
set_input_transition -max 0.2 [get_ports PCIE_RX_P*]
set_input_transition -min 0.1 [get_ports PCIE_RX_P*]
set_input_transition -max 0.25 [get_ports ETH_RX_P*]
set_input_transition -min 0.1 [get_ports ETH_RX_P*]
set_input_transition -max 0.2 [get_ports USB_RX_P*]
set_input_transition -min 0.1 [get_ports USB_RX_P*]
set_input_transition -max 0.5 [get_ports SYS_IN*]
set_input_transition -min 0.2 [get_ports SYS_IN*]

# Output Drive Strength (for output ports)
set_driving_cell -lib_cell INV_X4 -library standard_cells [get_ports DDR_DQ*]
set_driving_cell -lib_cell INV_X4 -library standard_cells [get_ports DDR_A*]
set_driving_cell -lib_cell INV_X3 -library standard_cells [get_ports PCIE_TX_P*]
set_driving_cell -lib_cell INV_X3 -library standard_cells [get_ports ETH_TX_P*]
set_driving_cell -lib_cell INV_X3 -library standard_cells [get_ports USB_TX_P*]
set_driving_cell -lib_cell INV_X2 -library standard_cells [get_ports SYS_OUT*]
set_driving_cell -lib_cell INV_X1 -library standard_cells [get_ports APB_OUT*]

#############################################################################
# 12. CLOCK GATING CHECKS
#############################################################################

# Enable Clock Gating Checks for All Gated Clocks
set_clock_gating_check -setup 0.1 -hold 0.05 [get_clocks clk_core]
set_clock_gating_check -setup 0.1 -hold 0.05 [get_clocks clk_npu]
set_clock_gating_check -setup 0.15 -hold 0.08 [get_clocks clk_gpu]
set_clock_gating_check -setup 0.2 -hold 0.1 [get_clocks clk_sys]
set_clock_gating_check -setup 0.15 -hold 0.08 [get_clocks clk_mem]

# High-Fanout Clock Gate Exceptions
set_clock_gating_check -setup 0.2 -hold 0.1 -high_fanout [get_pins u_clk_gate_cpu*_en]

#############################################################################
# 13. POWER DOMAIN CONSTRAINTS
#############################################################################

# Define Power Domains
create_power_domain -name PD_CORE -elements [get_cells u_cpu_cluster*]
create_power_domain -name PD_NPU -elements [get_cells u_npu*]
create_power_domain -name PD_GPU -elements [get_cells u_gpu*]
create_power_domain -name PD_MEM -elements [get_cells u_ddr_ctrl*]
create_power_domain -name PD_PERI -elements [get_cells u_peri*]

# Retention Register Constraints
set_retention_control -setup 0.5 -hold 0.2 [get_cells u_retention_*]
set_retention_data -min 0.5 [get_cells u_retention_*]

#############################################################################
# 14. IO STANDARD CONSTRAINTS
#############################################################################

# DDR5 I/O Standard
set_io_standard -name DDR5_IO -voltage 1.1 -interface_type HSTL_I_12 [get_ports DDR_*]

# PCIe I/O Standard
set_io_standard -name PCIE_IO -voltage 0.9 -interface_type PCIE [get_ports PCIE_*]

# Ethernet I/O Standard
set_io_standard -name ETH_IO -voltage 1.8 -interface_type LVDS [get_ports ETH_*]

# USB I/O Standard
set_io_standard -name USB_IO -voltage 0.9 -interface_type USB3 [get_ports USB_*]

# General Purpose I/O Standard
set_io_standard -name GPIO_IO -voltage 1.8 -interface_type LVCMOS18 [get_ports GPIO_*]

#############################################################################
# 15. CLOCK INTERCONNECT CONSTRAINTS
#############################################################################

# NoC Router Clock Constraints
set_clock_interconnect -max_delay 0.3 [get_clocks clk_sys]
set_clock_interconnect -min_delay 0.1 [get_clocks clk_sys]

# Core Cluster Interconnect
set_clock_interconnect -max_delay 0.2 [get_clocks clk_core]
set_clock_interconnect -min_delay 0.05 [get_clocks clk_core]

# NPU Interconnect
set_clock_interconnect -max_delay 0.2 [get_clocks clk_npu]
set_clock_interconnect -min_delay 0.05 [get_clocks clk_npu]

#############################################################################
# 16. SDC COMPLIANCE CHECKS
#############################################################################

# Check for unconstrained ports
set_units -time ns
set_max_delay 0 -from [all_inputs] -to [all_clocks]
set_max_delay 0 -from [all_clocks] -to [all_outputs]

# Report Configuration
report_clock -nosplit
report_clock_interconnect -nosplit
report_clock_groups -nosplit

#############################################################################
# END OF SDC FILE
#############################################################################
