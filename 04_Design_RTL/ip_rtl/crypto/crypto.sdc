# YaoGuang SoC Crypto Module SDC
# Design Constraints File
# Version: 1.0
# Date: 2026-01-18

###############################################################################
# 1. CLOCK DEFINITIONS
###############################################################################

# APB Interface Clock
create_clock -name apb_clk -period 10.0 [get_ports apb_clk]
set_clock_uncertainty -setup 0.15 [get_clocks apb_clk]
set_clock_uncertainty -hold 0.10 [get_clocks apb_clk]

# Crypto Engine Clock (main operational clock)
create_clock -name crypto_clk -period 5.0 [get_ports crypto_clk]
set_clock_uncertainty -setup 0.15 [get_clocks crypto_clk]
set_clock_uncertainty -hold 0.10 [get_clocks crypto_clk]

# TRNG Clock (independent clock domain)
create_clock -name trng_clk -period 20.0 [get_ports trng_clk]
set_clock_uncertainty -setup 0.15 [get_clocks trng_clk]
set_clock_uncertainty -hold 0.10 [get_clocks trng_clk]

# Generated clocks from clock dividers
# If internal dividers are used, add generated clock constraints here
# create_generated_clock -name crypto_clk_div2 -source [get_pins clk_gen_inst/div2] -divide_by 2 [get_clocks crypto_clk]

###############################################################################
# 2. CLOCK RELATIONSHIPS
###############################################################################

# Define clock groups for multi-corner analysis
set_clock_groups -asynchronous -group [get_clocks apb_clk]
set_clock_groups -asynchronous -group [get_clocks crypto_clk]
set_clock_groups -asynchronous -group [get_clocks trng_clk]

###############################################################################
# 3. INPUT DELAY CONSTRAINTS
###############################################################################

# APB Interface Input Delays (relative to apb_clk)
set_input_delay -clock apb_clk -add_delay 0.5 [get_ports {paddr[*] pwdata[*] pwrite psel penable presetn}]
set_input_delay -clock apb_clk -add_delay 1.0 [get_ports axis_tvalid]

# AXI4-Stream Input Delays (relative to crypto_clk)
set_input_delay -clock crypto_clk -add_delay 0.5 [get_ports {axis_tdata[*]}]
set_input_delay -clock crypto_clk -add_delay 0.5 [get_ports axis_tlast]
set_input_delay -clock crypto_clk -add_delay 1.0 [get_ports axis_tvalid]

###############################################################################
# 4. OUTPUT DELAY CONSTRAINTS
###############################################################################

# APB Interface Output Delays (relative to apb_clk)
set_output_delay -clock apb_clk -add_delay 0.5 [get_ports {prdata[*] pready crypto_intr}]
set_output_delay -clock apb_clk -add_delay 1.0 [get_ports pslverr]

# AXI4-Stream Output Delays (relative to crypto_clk)
set_output_delay -clock crypto_clk -add_delay 0.5 [get_ports {axis_tdata[*]}]
set_output_delay -clock crypto_clk -add_delay 0.5 [get_ports axis_tlast]
set_output_delay -clock crypto_clk -add_delay 1.0 [get_ports axis_tready]

###############################################################################
# 5. DRIVE AND LOAD CONSTRAINTS
###############################################################################

# Output drive strength
set_driving_cell -lib_cell $DRIVE_CELL [get_ports {prdata[*] pready crypto_intr axis_tready axis_tdata[*]}]

# Input load
set_load -pin_load 0.05 [get_ports {paddr[*] pwdata[*] pwrite psel penable axis_tvalid axis_tdata[*] axis_tlast}]

###############################################################################
# 6. MAX DELAY CONSTRAINTS
###############################################################################

# False path from reset to sequential elements
set_false_path -from [get_ports presetn]
set_false_path -from [get_ports crypto_rstn]
set_false_path -from [get_ports trng_rstn]

# Asynchronous clock domain crossing paths
set_false_path -from [get_clocks apb_clk] -to [get_clocks crypto_clk]
set_false_path -from [get_clocks crypto_clk] -to [get_clocks apb_clk]
set_false_path -from [get_clocks trng_clk] -to [get_clocks crypto_clk]
set_false_path -from [get_clocks crypto_clk] -to [get_clocks trng_clk]

# FIFO asynchronous read/write interfaces
set_false_path -through [get_ports -filter "name =~ *fifo*"]
set_max_delay -from [get_clocks crypto_clk] -to [get_clocks apb_clk] 5.0
set_max_delay -from [get_clocks apb_clk] -to [get_clocks crypto_clk] 5.0

###############################################################################
# 7. MIN DELAY CONSTRAINTS
###############################################################################

# Min delay for clock domain crossings
set_min_delay 0.5 -from [get_clocks crypto_clk] -to [get_clocks apb_clk]
set_min_delay 0.5 -from [get_clocks apb_clk] -to [get_clocks crypto_clk]

###############################################################################
# 8. PORT ATTRIBUTES
###############################################################################

# Set false path attributes for test ports
set_false_path_* [get_ports test]
set_dont_touch [get_ports test_*]

# Set constant values for unused ports if any
# set_driving_cell -lib_cell constant0 [get_ports unused_*]

###############################################################################
# 9. CLOCK LATENCY
###############################################################################

# Source latency (external clock tree)
set_clock_latency -source -early 0.1 [get_clocks apb_clk]
set_clock_latency -source -late 0.3 [get_clocks apb_clk]
set_clock_latency -source -early 0.1 [get_clocks crypto_clk]
set_clock_latency -source -late 0.3 [get_clocks crypto_clk]
set_clock_latency -source -early 0.1 [get_clocks trng_clk]
set_clock_latency -source -late 0.3 [get_clocks trng_clk]

###############################################################################
# 10. REGISTERS AND TIMING EXCEPTIONS
###############################################################################

# Don't touch specific registers during optimization
set_dont_touch [get_cells -hierarchical *secure_reg*]
set_dont_touch [get_cells -hierarchical *key_reg*]
set_dont_touch [get_cells -hierarchical *trng_reg*]

# Multi-cycle paths for slow operations
set_multicycle_path -setup 10 -from [get_clocks crypto_clk] -to [get_clocks crypto_clk] \
    -through [get_pipes crypto_top/crypto_core/rsa_ecc/*]
set_multicycle_path -hold 9 -from [get_clocks crypto_clk] -to [get_clocks crypto_clk] \
    -through [get_pipes crypto_top/crypto_core/rsa_ecc/*]

set_multicycle_path -setup 5 -from [get_clocks crypto_clk] -to [get_clocks crypto_clk] \
    -through [get_pipes crypto_top/crypto_core/ecc/*]
set_multicycle_path -hold 4 -from [get_clocks crypto_clk] -to [get_clocks crypto_clk] \
    -through [get_pipes crypto_top/crypto_core/ecc/*]

###############################################################################
# 11. MAX TRANSITION AND FANOUT
###############################################################################

# Maximum transition time
set_max_transition 0.5 [current_design]

# Maximum fanout
set_max_fanout 20 [current_design]

# Specific high-fanout nets
set_max_fanout 10 [get_nets -hierarchical *reset_net*]
set_max_fanout 15 [get_nets -hierarchical *clk_net*]

###############################################################################
# 12. AREA AND POWER CONSTRAINTS
###############################################################################

# Target area constraint (mm²)
set_max_area 1.0

# Power optimization
set_power_optimization -allow_shared true

###############################################################################
# 13. DESIGN RULE CHECKS
###############################################################################

# Enable design rule checks
set_drc_enable true

# Specific DRC rules
set_max_tels 0 [current_design]  # Maximum transition delay

###############################################################################
# 14. IO STANDARD CONSTRAINTS
###############################################################################

# Set IO standards (modify based on actual technology)
set_io_standard -lib_cell $IO_STANDARD [get_ports *]

# Specific port constraints
set_io_standard -lib_cell LVCMOS18 [get_ports {apb_clk presetn crypto_clk crypto_rstn trng_clk trng_rstn}]
set_io_standard -lib_cell LVCMOS18 [get_ports {paddr[*] pwdata[*] prdata[*]}]
set_io_standard -lib_cell LVCMOS18 [get_ports {pwrite psel penable pready pslverr crypto_intr}]
set_io_standard -lib_cell LVCMOS18 [get_ports {axis_tvalid axis_tready axis_tlast axis_tdata[*]}]

###############################################################################
# 15. OUTPUT ATTRIBUTES
###############################################################################

# Enable bus routing
set_bus_inference_style -separator {:} -width 4

# Enable report formatting
report_qor_state
report_timing -verbose
report_constraint -all_violators

###############################################################################
# END OF SDC FILE
###############################################################################
