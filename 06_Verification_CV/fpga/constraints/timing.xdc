###############################################################################
# YaoGuang SoC FPGA Timing Constraints - Versal ACAP
# Level: CV Verification Architect
# Date: 2026-01-18
# Target Device: xcvp1902-vsva2785-1MP-e-S
###############################################################################

###############################################################################
# Clock Constraints
###############################################################################

# Primary system clock - Main PLL output
create_clock -period 5.000 -name sys_clk [get_ports sys_clk_p]
create_clock -period 5.000 -name sys_clk_n [get_ports sys_clk_n]

# Derived clocks from clock manager
create_generated_clock -name cpu_clk \
    -source [get_pins -hierarchical -filter {name =~ *pll*CLKOUT0}] \
    -divide_by 1 -multiply_by 4 \
    [get_clocks -of_objects [get_pins -hierarchical -filter {name =~ *pll*CLKOUT0*}]]

create_generated_clock -name noc_clk \
    -source [get_pins -hierarchical -filter {name =~ *pll*CLKOUT1}] \
    -divide_by 1 -multiply_by 2 \
    [get_clocks -of_objects [get_pins -hierarchical -filter {name =~ *pll*CLKOUT1*}]]

create_generated_clock -name ddr_clk \
    -source [get_pins -hierarchical -filter {name =~ *ddr_pll*CLKOUT0}] \
    -divide_by 1 -multiply_by 2 \
    [get_clocks -of_objects [get_pins -hierarchical -filter {name =~ *ddr_pll*CLKOUT0*}]]

create_generated_clock -name peri_clk \
    -source [get_pins -hierarchical -filter {name =~ *pll*CLKOUT2}] \
    -divide_by 1 -multiply_by 1 \
    [get_clocks -of_objects [get_pins -hierarchical -filter {name =~ *pll*CLKOUT2*}]]

create_generated_clock -name safety_clk \
    -source [get_pins -hierarchical -filter {name =~ *safety_pll*CLKOUT0}] \
    -divide_by 1 -multiply_by 1 \
    [get_clocks -of_objects [get_pins -hierarchical -filter {name =~ *safety_pll*CLKOUT0*}]]

# Reference clocks
create_clock -period 10.000 -name ref_clk_200m [get_ports ref_clk_200m_p]
create_clock -period 8.000 -name ref_clk_125m [get_ports ref_clk_125m_p]

# DDR PHY clock (Differential)
create_clock -period 0.833 -name ddr_phy_clk [get_ports ddr_phy_clk_p]

###############################################################################
# Input/Output Constraints
###############################################################################

# System reset input
set_input_delay -clock sys_clk -max 2.0 [get_ports sys_rst_n]
set_input_delay -clock sys_clk -min 1.0 [get_ports sys_rst_n]

# UART inputs
set_input_delay -clock uart_clk -max 2.0 [get_ports uart_rxd]
set_input_delay -clock uart_clk -min 1.0 [get_ports uart_rxd]

# UART outputs
set_output_delay -clock uart_clk -max 2.0 [get_ports uart_txd]
set_output_delay -clock uart_clk -min 1.0 [get_ports uart_txd]

# GPIO inputs
set_input_delay -clock gpio_clk -max 1.5 [get_ports gpio_in*]
set_input_delay -clock gpio_clk -min 0.5 [get_ports gpio_in*]

# GPIO outputs
set_output_delay -clock gpio_clk -max 1.5 [get_ports gpio_out*]
set_output_delay -clock gpio_clk -min 0.5 [get_ports gpio_out*]

# SPI flash interface
set_input_delay -clock spi_clk -max 2.0 [get_ports spi_miso]
set_input_delay -clock spi_clk -min 1.0 [get_ports spi_miso]
set_output_delay -clock spi_clk -max 2.0 [get_ports spi_mosi]
set_output_delay -clock spi_clk -min 1.0 [get_ports spi_mosi]
set_output_delay -clock spi_clk -max 1.0 [get_ports spi_cs_n]
set_output_delay -clock spi_clk -min 0.0 [get_ports spi_cs_n]

# I2C interface
set_input_delay -clock i2c_clk -max 2.0 [get_ports i2c_sda_in]
set_input_delay -clock i2c_clk -min 1.0 [get_ports i2c_sda_in]
set_output_delay -clock i2c_clk -max 2.0 [get_ports i2c_sda_out]
set_output_delay -clock i2c_clk -min 1.0 [get_ports i2c_sda_out]

# DDR interface (DDR4)
set_input_delay -clock ddr_phy_clk -max 0.3 [get_ports ddr_ck_t*]
set_input_delay -clock ddr_phy_clk -min -0.1 [get_ports ddr_ck_t*]
set_input_delay -clock ddr_phy_clk -max 0.3 [get_ports ddr_ck_c*]
set_input_delay -clock ddr_phy_clk -min -0.1 [get_ports ddr_ck_c*]
set_input_delay -clock ddr_phy_clk -max 0.4 [get_ports ddr_dq[*]]
set_input_delay -clock ddr_phy_clk -min -0.1 [get_ports ddr_dq[*]]
set_input_delay -clock ddr_phy_clk -max 0.3 [get_ports ddr_dqs_t*]
set_input_delay -clock ddr_phy_clk -min -0.1 [get_ports ddr_dqs_t*]

set_output_delay -clock ddr_phy_clk -max 0.4 [get_ports ddr_command*]
set_output_delay -clock ddr_phy_clk -min -0.1 [get_ports ddr_command*]
set_output_delay -clock ddr_phy_clk -max 0.4 [get_ports ddr_address*]
set_output_delay -clock ddr_phy_clk -min -0.1 [get_ports ddr_address*]
set_output_delay -clock ddr_phy_clk -max 0.4 [get_ports ddr_cke*]
set_output_delay -clock ddr_phy_clk -min -0.1 [get_ports ddr_cke*]

# Ethernet RMII
set_input_delay -clock eth_rx_clk -max 2.0 [get_ports eth_rxd*]
set_input_delay -clock eth_rx_clk -min 1.0 [get_ports eth_rxd*]
set_output_delay -clock eth_tx_clk -max 2.0 [get_ports eth_txd*]
set_output_delay -clock eth_tx_clk -min 1.0 [get_ports eth_txd*]

# USB PHY
set_input_delay -clock usb_clk -max 2.0 [get_ports usb_data*]
set_input_delay -clock usb_clk -min 1.0 [get_ports usb_data*]
set_output_delay -clock usb_clk -max 2.0 [get_ports usb_data*]
set_output_delay -clock usb_clk -min 1.0 [get_ports usb_data*]

###############################################################################
# False Path Constraints
###############################################################################

# Asynchronous reset paths
set_false_path -from [get_ports sys_rst_n] -to [all_registers]
set_false_path -from [get_ports por_rst_n] -to [all_registers]

# CDC paths between clock domains
set_false_path -from [get_clocks cpu_clk] -to [get_clocks noc_clk]
set_false_path -from [get_clocks noc_clk] -to [get_clocks cpu_clk]
set_false_path -from [get_clocks cpu_clk] -to [get_clocks peri_clk]
set_false_path -from [get_clocks peri_clk] -to [get_clocks cpu_clk]
set_false_path -from [get_clocks ddr_clk] -to [get_clocks cpu_clk]
set_false_path -from [get_clocks cpu_clk] -to [get_clocks ddr_clk]

# Reset synchronizer paths
set_false_path -through [get_pins -hierarchical -filter {name =~ *reset_sync*/*D}]

# Multi-cycle paths for slow peripherals
set_false_path -from [get_clocks sys_clk] -to [get_clocks peri_clk]
set_false_path -from [get_clocks peri_clk] -to [get_clocks sys_clk]

###############################################################################
# Multi-Cycle Path Constraints
###############################################################################

# Slow peripheral registers
set_multicycle_path -from [get_clocks sys_clk] -to [get_clocks peri_clk] -setup 2
set_multicycle_path -from [get_clocks sys_clk] -to [get_clocks peri_clk] -hold 1

set_multicycle_path -from [get_clocks peri_clk] -to [get_clocks sys_clk] -setup 2
set_multicycle_path -from [get_clocks peri_clk] -to [get_clocks sys_clk] -hold 1

# Debug logic paths (relaxed timing)
set_multicycle_path -from [get_clocks sys_clk] -to [get_clocks sys_clk] \
    -through [get_pins -hierarchical -filter {name =~ *debug*/*}] -setup 2

###############################################################################
# Maximum Delay Constraints
###############################################################################

# Inter-clock domain paths
set_max_delay -from [get_clocks cpu_clk] -to [get_clocks noc_clk] 5.000
set_max_delay -from [get_clocks noc_clk] -to [get_clocks cpu_clk] 5.000
set_max_delay -from [get_clocks cpu_clk] -to [get_clocks ddr_clk] 3.000
set_max_delay -from [get_clocks ddr_clk] -to [get_clocks cpu_clk] 3.000

# Asynchronous FIFO paths
set_max_delay -from [get_pins -hierarchical -filter {name =~ *async_fifo*/*WRCLK*}] \
    -to [get_pins -hierarchical -filter {name =~ *async_fifo*/*RDCLK*}] 10.000

###############################################################################
# Clock Group Constraints
###############################################################################

# Independent clock groups
set_clock_groups -asynchronous \
    -group [get_clocks sys_clk] \
    -group [get_clocks cpu_clk] \
    -group [get_clocks noc_clk] \
    -group [get_clocks ddr_clk] \
    -group [get_clocks peri_clk] \
    -group [get_clocks safety_clk]

# Exclusive clock groups (mutually exclusive)
set_clock_groups -exclusive \
    -group [get_clocks cpu_clk] \
    -group [get_clocks cpu_clk_div2]

###############################################################################
# Port Delay Constraints
###############################################################################

# DDR memory interface delays
set_input_delay -clock ddr_phy_clk -max 0.5 [get_ports ddr_reset_n]
set_output_delay -clock ddr_phy_clk -max 0.5 [get_ports ddr_reset_n]

# Clock enable delays
set_output_delay -clock sys_clk -max 1.0 [get_ports clk_en*]
set_output_delay -clock sys_clk -min 0.0 [get_ports clk_en*]

###############################################################################
# IO Standard Constraints
###############################################################################

# DDR4 IO standard
set_io_standard -standard HSTL_18_II -bank {DDR_BANK_0 DDR_BANK_1}

# LVCMOS for general purpose IO
set_io_standard -standard LVCMOS18 -bank {GPIO_BANK_0 GPIO_BANK_1 GPIO_BANK_2}

# LVDS for differential clocks
set_io_standard -standard LVDS -bank {SYSCLK_BANK}

# SSTL for DDR3/DDR4 (legacy)
set_io_standard -standard SSTL135 -bank {DDR_LEGACY_BANK}

###############################################################################
# Signal Integrity Constraints
###############################################################################

# ODT settings for DDR
set_property IODELAY_GROUP DDR_IODELAY_GROUP [get_cells -hierarchical -filter {name =~ *ddr_phy*}]

# Slew rates for fast signals
set_property SLEW FAST [get_ports -filter {name =~ *clk*}]
set_property SLEW SLOW [get_ports -filter {name =~ *rst*}]

###############################################################################
# Physical Constraints
###############################################################################

# Location constraints for critical macros
set_property LOC RAMB36_X*Y* [get_cells -hierarchical -filter {name =~ *dist_mem*}]

# DSP slice location preferences
set_property LOC DSP48E2_X*Y* [get_cells -hierarchical -filter {name =~ *dsp*}]

# I/O register packing
set_property IOB TRUE [get_cells -hierarchical -filter {name =~ *iob_reg*}]

###############################################################################
# DRC Exceptions
###############################################################################

# Allow unconstrained paths for debug logic
set_property DONT_TOUCH TRUE [get_cells -hierarchical -filter {name =~ *debug_unit*}]

# Mark timing ignore for JTAG
set_false_path -through [get_pins -hierarchical -filter {name =~ *jtag*/*}]
set_false_path -through [get_pins -hierarchical -filter {name =~ *boundary_scan*/*}]

###############################################################################
# report_timing Summary
###############################################################################

# Custom timing report settings
set_msg_id -id {Timings-6} -new_severity INFO
set_msg_id -id {Timings-31} -new_severity INFO

# Enable advanced timing analysis
set_enable_energy_analysis 0
