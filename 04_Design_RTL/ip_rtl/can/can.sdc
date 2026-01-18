# CAN FD Controller SDC Constraints

# Created: 2026-01-19
# Target Process: TBD (28nm or 22nm FD-SOI)
# Clock Frequency: 200MHz (APB), 80MHz (CAN Core)

###############################################################################
# Create Clocks
###############################################################################

# APB Interface Clock
create_clock -name clk_apb -period 5.0 [get_ports clk_apb]

# CAN Core Clock (from PLL, 80MHz nominal)
create_clock -name clk_can -period 12.5 [get_ports clk_can]

# Reference Clock (for bit timing, typically 40-80MHz)
create_clock -name clk_ref -period 12.5 [get_ports clk_ref]

# Test Clock
create_clock -name clk_test -period 2.5 [get_ports clk_test]

###############################################################################
# Clock Groups
###############################################################################

# Asynchronous clock domains
set_clock_groups -asynchronous \
    -group [get_clocks clk_apb] \
    -group [get_clocks clk_can] \
    -group [get_clocks clk_ref] \
    -group [get_clocks clk_test]

###############################################################################
# Input/Output Delays
###############################################################################

# CAN TX Output Delay (data output after clock edge)
set_output_delay -clock clk_can -max 4.0 [get_ports tx*]
set_output_delay -clock clk_can -min 1.0 [get_ports tx*]

# CAN RX Input Delay (data input before clock edge)
set_input_delay -clock clk_can -max 3.0 [get_ports rx*]
set_input_delay -clock clk_can -min 1.0 [get_ports rx*]

# APB Interface Input Delays
set_input_delay -clock clk_apb -max 2.0 [get_ports paddr*]
set_input_delay -clock clk_apb -max 2.0 [get_ports pwrite]
set_input_delay -clock clk_apb -max 2.0 [get_ports pwdata*]
set_input_delay -clock clk_apb -max 2.0 [get_ports psel*]
set_input_delay -clock clk_apb -max 2.0 [get_ports penable]

set_input_delay -clock clk_apb -min 0.5 [get_ports paddr*]
set_input_delay -clock clk_apb -min 0.5 [get_ports pwrite]
set_input_delay -clock clk_apb -min 0.5 [get_ports pwdata*]
set_input_delay -clock clk_apb -min 0.5 [get_ports psel*]
set_input_delay -clock clk_apb -min 0.5 [get_ports penable]

# APB Interface Output Delays
set_output_delay -clock clk_apb -max 4.0 [get_ports prdata*]
set_output_delay -clock clk_apb -max 4.0 [get_ports pready]
set_output_delay -clock clk_apb -max 4.0 [get_ports pslverr]
set_output_delay -clock clk_apb -min 0.5 [get_ports prdata*]
set_output_delay -clock clk_apb -min 0.5 [get_ports pready]
set_output_delay -clock clk_apb -min 0.5 [get_ports pslverr]

###############################################################################
# False Paths
###############################################################################

# Reset paths are not timing critical
set_false_path -from [get_ports rst_n] -to [all_registers]
set_false_path -from [get_ports rst_apb_n] -to [all_registers]

# Asynchronous reset release
set_false_path -from [get_ports arst_n] -to [all_registers -clock_nodes]

# Test mode paths
set_false_path -from [get_ports test_mode]
set_false_path -from [get_ports scan_enable]

# Staggered reset for multi-channel (reset deassertion offset)
set_false_path -from [get_ports rst_n] -to [get_registers -filter "rst_n_reg[*]"]

###############################################################################
# Multicycle Paths
###############################################################################

# APB to register write path (PREADY can extend transfer)
set_multicycle_path -setup 2 -from [get_ports psel*] -to [get_registers *paddr_reg*]
set_multicycle_path -hold 1 -from [get_ports psel*] -to [get_registers *paddr_reg*]

# Register to APB read path
set_multicycle_path -setup 1 -from [get_registers *prdata*] -to [get_ports prdata*]
set_multicycle_path -hold 0 -from [get_registers *prdata*] -to [get_ports prdata*]

###############################################################################
# Maximum Delay Constraints
###############################################################################

# Reset to clock domain crossing
set_max_delay 10.0 -from [get_ports rst_n] -to [all_registers]
set_max_delay 10.0 -from [get_ports rst_apb_n] -to [all_registers]

# Clock domain crossing paths
set_max_delay -from [get_clocks clk_apb] -to [get_clocks clk_can] 15.0
set_max_delay -from [get_clocks clk_can] -to [get_clocks clk_apb] 15.0

###############################################################################
# Driving Cells / Load Constraints
###############################################################################

# Output driving strength
set_driving_cell -lib_cell BUF_X4 -library standard_cells [get_ports tx*]
set_driving_cell -lib_cell BUF_X4 -library standard_cells [get_ports pready]
set_driving_cell -lib_cell BUF_X4 -library standard_cells [get_ports prdata*]
set_driving_cell -lib_cell BUF_X4 -library standard_cells [get_ports interrupt*]

# Input transition times
set_input_transition -min 0.05 -library standard_cells [get_ports rx*]
set_input_transition -max 0.2 -library standard_cells [get_ports rx*]
set_input_transition -min 0.05 -library standard_cells [get_ports clk_can]
set_input_transition -max 0.2 -library standard_cells [get_ports clk_can]

# Output loads
set_load -pin_load 0.05 [get_ports tx*]
set_load -pin_load 0.05 [get_ports pready]
set_load -pin_load 0.05 [get_ports prdata*]
set_load -pin_load 0.05 [get_ports interrupt*]

###############################################################################
# Clock Latency
###############################################################################

# Network latency for generated clocks
set_clock_latency -source -max 0.5 [get_clocks clk_can]
set_clock_latency -source -min 0.2 [get_clocks clk_can]
set_clock_latency -max 0.3 [get_clocks clk_can]
set_clock_latency -min 0.1 [get_clocks clk_can]

###############################################################################
# Clock Uncertainty
###############################################################################

# Jitter and uncertainty
set_clock_uncertainty -setup 0.2 [get_clocks clk_apb]
set_clock_uncertainty -hold 0.1 [get_clocks clk_apb]
set_clock_uncertainty -setup 0.3 [get_clocks clk_can]
set_clock_uncertainty -hold 0.15 [get_clocks clk_can]
set_clock_uncertainty -setup 0.15 [get_clocks clk_ref]
set_clock_uncertainty -hold 0.08 [get_clocks clk_ref]

###############################################################################
# Area Constraints
###############################################################################

# Target area for CAN controller (single channel)
set_max_area 150000  # ~150K um^2 for single CAN channel

# Group area constraint for multi-channel
set_max_area -group can_top 500000  # ~500K um^2 for 4-channel CAN

###############################################################################
# Power Constraints
###############################################################################

# Dynamic power budget
set_max_dynamic_power 50 mW

# Leakage power budget
set_max_leakage_power 5 mW

###############################################################################
# Timing Exceptions
###############################################################################

# Disable timing for instantiated memory if using RAM compiler
set_false_path -through [get_pins -hierarchical -filter "name=~*mem*"]
set_false_path -through [get_pins -hierarchical -filter "name=~*fifo*"]

# Asynchronous FIFO timing (CDC handled internally)
set_false_path -through [get_cells -hierarchical *async_fifo*]

###############################################################################
# IO Standard
###############################################################################

# Set IO standards (adjust based on target process)
set_io_standard -lib_cell LVTTL18 [get_ports clk_apb clk_can clk_ref rst_n rst_apb_n]
set_io_standard -lib_cell LVTTL18 [get_ports paddr* pwrite pwdata* psel* penable pready]
set_io_standard -lib_cell LVTTL18 [get_ports prdata* pslverr interrupt*]
set_io_standard -lib_cell LVTTL18 [get_ports tx* rx*]

# Set IO delay (if using input buffers with delays)
set_input_delay -clock clk_can -max 2.0 -add_delay [get_ports rx*]
set_output_delay -clock clk_can -max 2.0 -add_delay [get_ports tx*]

###############################################################################
# Design Constraints for Scan/DFT
###############################################################################

# Scan chain definitions
set_scan_configuration -chain_count 4

# Test clock
create_clock -name clk_scan -period 10.0 [get_ports clk_scan]

# ATPG constraints
set_dft_signal -view existing_dft -type ScanClock -port clk_scan
set_dft_signal -view existing_dft -type Reset -port rst_n
set_dft_signal -view existing_dft -type Set -port arst_n

###############################################################################
# Sign-off Corner Constraints
###############################################################################

# Multiple corners (typical/min/max)
set_operating_conditions -max tt_1p2v_125c
set_operating_conditions -min ss_1p0v_m40c
set_operating_conditions -typical ff_1p4v_m40c

###############################################################################
# End of SDC Constraints
###############################################################################
