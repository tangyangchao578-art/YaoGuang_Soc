#=============================================================================
# Safety Island SDC Constraints
# ASIL-D Safety Critical - Clock and Timing Constraints
#=============================================================================

#=============================================================================
# Create Clocks
#=============================================================================
create_clock -name clk_safety -period 1.0 [get_ports clk_safety_i]
create_clock -name clk_main   -period 1.0 [get_ports clk_main_i]

#=============================================================================
# Clock Groups (Asynchronous Clock Domains)
#=============================================================================
set_clock_groups -asynchronous \
    -group [get_clocks clk_safety] \
    -group [get_clocks clk_main]

#=============================================================================
# Input/Output Delays
#=============================================================================
set_input_delay  -clock clk_safety 0.5 [get_ports clk_safety_i]
set_input_delay  -clock clk_main   0.5 [get_ports clk_main_i]
set_input_delay  -clock clk_safety 0.5 [get_ports rst_n_safety_i]
set_input_delay  -clock clk_main   0.5 [get_ports rst_n_main_i]

set_output_delay -clock clk_safety 0.5 [get_ports clk_safety_gated_o]
set_output_delay -clock clk_safety 0.5 [get_ports rst_n_safety_synced_o]

#=============================================================================
# False Paths
#=============================================================================
set_false_path -from [get_ports scan_en_i]   -to [all_registers]
set_false_path -from [get_ports mbist_en_i]  -to [all_registers]
set_false_path -from [get_ports bist_start_i] -to [all_registers]

#=============================================================================
# Multi-Cycle Paths
#=============================================================================
set_multicycle_path -setup 2 -from [get_pins */u_r52_lockstep/*] -to [get_pins */u_ecc_ctrl/*]
set_multicycle_path -hold 1  -from [get_pins */u_r52_lockstep/*] -to [get_pins */u_ecc_ctrl/*]

set_multicycle_path -setup 2 -from [get_pins */u_ecc_ctrl/*] -to [get_pins */u_err_rpt/*]
set_multicycle_path -hold 1  -from [get_pins */u_ecc_ctrl/*] -to [get_pins */u_err_rpt/*]

#=============================================================================
# Maximum Delay (Data to Output)
#=============================================================================
set_max_delay 0.8 -from [all_inputs] -to [all_outputs]

#=============================================================================
# Clock Uncertainty
#=============================================================================
set_clock_uncertainty -setup 0.1 [get_clocks clk_safety]
set_clock_uncertainty -hold 0.05 [get_clocks clk_safety]
set_clock_uncertainty -setup 0.1 [get_clocks clk_main]
set_clock_uncertainty -hold 0.05 [get_clocks clk_main]

#=============================================================================
# Driving Cell (IO Constraints)
#=============================================================================
set_driving_cell -lib_cell BUF_X4 [get_ports {clk_safety_i, clk_main_i, rst_n_safety_i, rst_n_main_i}]
set_load -pin_load 0.05 [get_ports {watchdog_pulse_o, error_valid_o}]

#=============================================================================
# Area Constraints (Safety Island Target Area)
#=============================================================================
set_max_area 4.0

#=============================================================================
# Power Constraints
#============================================================================>
set_max_dynamic_power 0.5

#=============================================================================
# Timing Exceptions for Reset Signals
#=============================================================================
set_false_path -from [get_ports rst_n_main_i] -to [get_pins */u_safe_clk_rst/rst_sync_chain[*]/D]
set_false_path -from [get_ports rst_n_safety_i] -to [get_pins */u_safe_clk_rst/rst_sync_chain[*]/D]

#=============================================================================
# DFT Constraints
#=============================================================================
set_dft_signal -view existing -type ScanIn -port scan_en_i
set_dft_signal -view existing -type ScanOut -port bist_done_o

#=============================================================================
# Voltage and Temperature (Corner Definitions)
#============================================================================>
set_operating_conditions -max tt_1p2v_125c -min ss_0p9v_m40c

#=============================================================================
# Output Generation
#=============================================================================
report_timing -delay_type max -max_paths 10 > safety_island_timing_max.rpt
report_timing -delay_type min -max_paths 10 > safety_island_timing_min.rpt
report_clock   > clock_report.rpt
