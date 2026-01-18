# NoC SDC Constraints
# YaoGuang SoC Network-on-Chip
# Version: V1.0
# Date: 2026-01-19

###############################################################################
# 1. Clock Definitions
###############################################################################

# Main NoC Clock
create_clock -name clk -period 0.5 [get_ports clk]

# Generated clocks for divided domains
create_generated_clock -name clk_half -source [get_ports clk] -divide_by 2 [get_pins clk_half_reg/Q]

###############################################################################
# 2. Clock Uncertainty
###############################################################################

# Clock uncertainty for setup
set_clock_uncertainty -rise_to_fall 0.05 [get_clocks clk]
set_clock_uncertainty -fall_to_rise 0.05 [get_clocks clk]

# Additional uncertainty for clock domain crossings
set_clock_uncertainty -from [get_clocks clk] -to [get_clocks clk_half] 0.1

###############################################################################
# 3. Input/Output Delays
###############################################################################

# Input delays (Setup)
set_input_delay -clock clk -max 0.2 [get_ports vc_valid_in*]
set_input_delay -clock clk -max 0.3 [get_ports vc_data_in*]
set_input_delay -clock clk -max 0.25 [get_ports vc_id_in*]
set_input_delay -clock clk -max 0.25 [get_ports vc_prio_in*]

# Input delays (Hold)
set_input_delay -clock clk -min -0.1 [get_ports vc_valid_in*]
set_input_delay -clock clk -min -0.15 [get_ports vc_data_in*]
set_input_delay -clock clk -min -0.1 [get_ports vc_id_in*]
set_input_delay -clock clk -min -0.1 [get_ports vc_prio_in*]

# Output delays (Setup)
set_output_delay -clock clk -max 0.3 [get_ports vc_valid_out*]
set_output_delay -clock clk -max 0.4 [get_ports vc_data_out*]
set_output_delay -clock clk -max 0.35 [get_ports vc_id_out*]
set_output_delay -clock clk -max 0.35 [get_ports vc_prio_out*]
set_output_delay -clock clk -max 0.3 [get_ports port_busy*]
set_output_delay -clock clk -max 0.3 [get_ports vc_credits*]

# Output delays (Hold)
set_output_delay -clock clk -min -0.15 [get_ports vc_valid_out*]
set_output_delay -clock clk -min -0.2 [get_ports vc_data_out*]
set_output_delay -clock clk -min -0.15 [get_ports vc_id_out*]
set_output_delay -clock clk -min -0.15 [get_ports vc_prio_out*]
set_output_delay -clock clk -min -0.15 [get_ports port_busy*]
set_output_delay -clock clk -min -0.15 [get_ports vc_credits*]

###############################################################################
# 4. False Paths
###############################################################################

# Asynchronous reset is not timed
set_false_path -from [get_ports rst_n]
set_false_path -to [get_ports sys_error]

# Debug signals
set_false_path -from [get_ports vc_pkt_id_in*]
set_false_path -to [get_ports vc_pkt_id_out*]

###############################################################################
# 5. Multi-Cycle Paths
###############################################################################

# Credit counter updates can take multiple cycles
set_multicycle_path -setup 2 -from [get_pins credit_count*/Q] -to [get_pins credit_count*/D]
set_multicycle_path -hold 1 -from [get_pins credit_count*/Q] -to [get_pins credit_count*/D]

# FIFO read/write synchronization
set_multicycle_path -setup 2 -from [get_pins vc_fifo*/wr_ptr/Q] -to [get_pins vc_fifo*/rd_ptr/D]
set_multicycle_path -hold 1 -from [get_pins vc_fifo*/wr_ptr/Q] -to [get_pins vc_fifo*/rd_ptr/D]

###############################################################################
# 6. Maximum Capacitance
###############################################################################

set_max_capacitance -clock clk 0.5 [get_ports vc_data_out*]

###############################################################################
# 7. Maximum Transition
###############################################################################

set_max_transition -clock clk 0.3 [all_inputs]
set_max_transition -clock clk 0.3 [all_outputs]

###############################################################################
# 8. Drive Strength
###############################################################################

set_drive 0.1 [get_ports vc_data_out*]
set_drive 0.2 [get_ports vc_valid_out*]
set_drive 0.2 [get_ports vc_id_out*]
set_drive 0.2 [get_ports vc_prio_out*]

set_drive -min 0.1 [get_ports vc_data_out*]
set_drive -min 0.2 [get_ports vc_valid_out*]

###############################################################################
# 9. Load Model
###############################################################################

set_load -pin_load 0.02 [get_ports vc_data_out*]
set_load -pin_load 0.01 [get_ports vc_valid_out*]
set_load -pin_load 0.01 [get_ports vc_id_out*]
set_load -pin_load 0.01 [get_ports vc_prio_out*]

###############################################################################
# 10. Operating Conditions
###############################################################################

set_operating_conditions -max tt_125c_1v2 -min tt_n40c_1v1

###############################################################################
# 11. Wire Load Models
###############################################################################

set_wire_load_model -name tt -min {tt}
set_wire_load_model -name tt -max {tt}

###############################################################################
# 12. Design Constraints File
###############################################################################

# Set design name
set_design_name noc_top

# Set top level module
current_design noc_top

###############################################################################
# 13. Area Constraints (Target: 8mm²)
###############################################################################

set_max_area 8000000

###############################################################################
# 14. Power Constraints (Target: 3W)
###############################################################################

set_max_power -dynamic 2.7 -static 0.75

###############################################################################
# 15. Register Balancing
###############################################################################

set_register_balancing -none

###############################################################################
# 16. Critical Range
###############################################################################

set_critical_range 0.1

###############################################################################
# 17. Timing Disable
###############################################################################

# Disable timing for BIST interfaces if present
set_timing_derive -ignore_bidirectional

###############################################################################
# 18. Input Transition Time
###############################################################################

set_input_transition -clock clk -max 0.1 [get_ports vc_data_in*]
set_input_transition -clock clk -max 0.05 [get_ports vc_valid_in*]

###############################################################################
# 19. Output Slew Constraints
###############################################################################

set_max_slew -clock clk 0.2 [get_outputs]
set_max_slew -clock clk 0.15 [get_ports vc_data_out*]

###############################################################################
# 20. DRC Constraints
###############################################################################

# Enable clock gating checks
set_clock_gating_check -setup 0.05 -hold 0.05

# Enable recovery/removal checks
set_recovery_check -setup 0.05 -hold 0.05 [get_ports rst_n]

###############################################################################
# End of SDC Constraints
###############################################################################
