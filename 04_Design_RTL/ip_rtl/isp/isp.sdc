# ============================================================
# Project: YaoGuang ISP
# SDC Constraints for ISP Top Level
# ============================================================

# ============================================================
# Clock Constraints
# ============================================================

# Main system clock (CSI-2 RX)
create_clock -name clk_pixel -period 5.556 [get_ports clk_pixel_i]
# 4K@60fps = 148.5MHz pixel clock
# Period = 1000/148.5 = 6.73ns, using 5.556ns for 180MHz (4K@60 with overhead)

# CSI-2 clock (from PHY)
create_clock -name csi_clk -period 0.222 [get_ports csi_clk_p_i]
# 4.5 Gbps / lane = 2.25 GHz DDR = 0.444ns period per edge, 0.222ns per edge

# ============================================================
# Clock Groups
# ============================================================

# Asynchronous clock domains
set_clock_groups -asynchronous -group {clk_pixel} -group {clk_i}
set_clock_groups -asynchronous -group {csi_clk} -group {clk_pixel}
set_clock_groups -asynchronous -group {csi_clk} -group {clk_i}

# ============================================================
# Input/Output Delay Constraints
# ============================================================

# MIPI CSI-2 Data Inputs (D-PHY)
set_input_delay -clock csi_clk -add_delay 0.100 [get_ports csi_d_p_i*]
set_input_delay -clock csi_clk -add_delay -0.100 [get_ports csi_d_n_i*]

# MIPI CSI-2 Clock Input
set_input_delay -clock csi_clk -add_delay 0.050 [get_ports csi_clk_p_i]
set_input_delay -clock csi_clk -add_delay -0.050 [get_ports csi_clk_n_i]

# Output delays for formatter
set_output_delay -clock clk_pixel -add_delay 0.500 [get_ports out_data_o*]
set_output_delay -clock clk_pixel -add_delay 0.500 [get_ports out_valid_o]
set_output_delay -clock clk_pixel -add_delay 0.500 [get_ports out_pixel_x_o*]
set_output_delay -clock clk_pixel -add_delay 0.500 [get_ports out_pixel_y_o*]
set_output_delay -clock clk_pixel -add_delay 0.500 [get_ports out_frame_start_o]
set_output_delay -clock clk_pixel -add_delay 0.500 [get_ports out_frame_end_o]

# ============================================================
# False Path Constraints
# ============================================================

# Configuration registers (async)
set_false_path -from [get_ports cfg_reg_*]
set_false_path -to [get_ports cfg_reg_*]

# Status signals
set_false_path -from [get_ports init_done_o]
set_false_path -from [get_ports overflow_o]
set_false_path -from [get_ports csi_lock_o]

# ============================================================
# Maximum Delay Constraints
# ============================================================

# Pixel pipeline (critical path)
set_max_delay -from [get_pixels *pixel*] -to [get_pixels *pixel*] 6.000
set_max_delay -from [get_pixels *rgb*] -to [get_pixels *rgb*] 6.000

# Statistics path (can tolerate more latency)
set_max_delay -from [get_pixels *stats*] -to [get_pixels *stats*] 10.000

# ============================================================
# Multicycle Path Constraints
# ============================================================

# ISP pipeline stages (multi-cycle for relaxation)
set_multicycle_path -setup -end 2 -from [get_pixels *pipeline*] -to [get_pixels *pipeline*]
set_multicycle_path -hold -end 1 -from [get_pixels *pipeline*] -to [get_pixels *pipeline*]

# Frame buffer accesses
set_multicycle_path -setup -end 3 -from [get_pixels *buffer*] -to [get_pixels *buffer*]
set_multicycle_path -hold -end 2 -from [get_pixels *buffer*] -to [get_pixels *buffer*]

# ============================================================
# Drive Strength Constraints
# ============================================================

# Output drive strength
set_drive 4 [get_ports out_data_o*]
set_drive 4 [get_ports out_valid_o]
set_drive 4 [get_ports out_pixel_*_o*]
set_drive 4 [get_ports out_frame_*_o]

# CSI-2 inputs (should be terminated)
set_drive 20 [get_ports csi_d_p_i*]
set_drive 20 [get_ports csi_d_n_i*]
set_drive 20 [get_ports csi_clk_p_i]
set_drive 20 [get_ports csi_clk_n_i]

# ============================================================
# Load Constraints
# ============================================================

# Expected capacitive loads
set_load -pin_load 0.5 [get_ports out_data_o*]
set_load -pin_load 0.5 [get_ports out_valid_o]
set_load -pin_load 0.5 [get_ports out_pixel_*_o*]
set_load -pin_load 0.5 [get_ports out_frame_*_o]

# CSI-2 inputs (differential)
set_load -pin_load 0.2 [get_ports csi_d_p_i*]
set_load -pin_load 0.2 [get_ports csi_d_n_i*]
set_load -pin_load 0.2 [get_ports csi_clk_p_i]
set_load -pin_load 0.2 [get_ports csi_clk_n_i]

# ============================================================
# Transition Time Constraints
# ============================================================

set_max_transition 0.200 [get_ports csi_d_p_i*]
set_max_transition 0.200 [get_ports csi_d_n_i*]
set_max_transition 0.200 [get_ports csi_clk_p_i]
set_max_transition 0.200 [get_ports csi_clk_n_i]
set_max_transition 0.500 [get_ports out_*]

# ============================================================
# Area Constraints
# ============================================================

set_max_area 4.0

# ============================================================
# Power Constraints
# ============================================================

set_max_dynamic_power 4.0

# ============================================================
# Clock Uncertainty
# ============================================================

set_clock_uncertainty 0.100 clk_pixel
set_clock_uncertainty 0.020 csi_clk

# ============================================================
# Port Attributes
# ============================================================

# Differential pairs
set_isfixed true [get_ports csi_d_p_i*]
set_isfixed true [get_ports csi_d_n_i*]
set_isfixed true [get_ports csi_clk_p_i]
set_isfixed true [get_ports csi_clk_n_i]

# ============================================================
# Timing Exceptions
# ============================================================

# Reset signals (async)
set_false_path -from [get_ports rst_n_i]
set_false_path -from [get_ports rst_pixel_n_i]

# ============================================================
# Design Rule Checks
# ============================================================

set_max_fanout 10 [get_ports csi_d_p_i*]
set_max_fanout 10 [get_ports csi_d_n_i*]
set_max_fanout 10 [get_ports csi_clk_p_i]
set_max_fanout 10 [get_ports csi_clk_n_i]

# ============================================================
# End of SDC
# ============================================================
