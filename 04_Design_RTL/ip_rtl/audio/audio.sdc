# Audio Module SDC (Synopsys Design Constraints)
# YaoGuang SoC - Audio Subsystem
# Version: 1.0
# Date: 2026-01-18

###############################################################################
# SECTION 1: CLOCK DEFINITIONS
###############################################################################

# Main system clock (APB interface)
create_clock -period 10.000 -name pclk [get_ports pclk]

# Audio domain clock
create_clock -period 5.000 -name audio_clk [get_clocks audio_clk]

# AXI-Stream TX clock
create_clock -period 4.000 -name tx_axis_aclk [get_ports tx_axis_aclk]

# AXI-Stream RX clock
create_clock -period 4.000 -name rx_axis_aclk [get_ports rx_axis_aclk]

# I2S Bit Clock (derived from audio_clk)
create_generated_clock -name i2s_bclk \
    -source [get_pins -hierarchical *i2s_controller*] \
    -divide_by 2 [get_ports i2s_bclk_o]

# TDM Bit Clock
create_generated_clock -name tdm_bclk \
    -source [get_pins -hierarchical *tdm_controller*] \
    -divide_by 2 [get_ports tdm_bclk_o]

# PDM Clock
create_clock -period 20.000 -name pdm_clk [get_ports pdm_clk]

###############################################################################
# SECTION 2: CLOCK GROUPS
###############################################################################

# Asynchronous clock groups
set_clock_groups -asynchronous \
    -group [get_clocks pclk] \
    -group [get_clocks audio_clk] \
    -group [get_clocks tx_axis_aclk] \
    -group [get_clocks rx_axis_aclk] \
    -group [get_clocks pdm_clk]

###############################################################################
# SECTION 3: INPUT/OUTPUT DELAYS
###############################################################################

# Output delays for APB interface
set_output_delay -clock pclk -max 2.000 [get_ports prdata]
set_output_delay -clock pclk -min 0.500 [get_ports prdata]
set_output_delay -clock pclk -max 1.000 [get_ports pready]

set_input_delay -clock pclk -max 2.000 [get_ports paddr]
set_input_delay -clock pclk -max 2.000 [get_ports pwdata]
set_input_delay -clock pclk -max 1.000 [get_ports pwrite]
set_input_delay -clock pclk -max 1.000 [get_ports psel]
set_input_delay -clock pclk -max 1.000 [get_ports penable]

# Output delays for AXI-Stream TX
set_output_delay -clock tx_axis_aclk -max 2.000 [get_ports tx_axis_tdata*]
set_output_delay -clock tx_axis_aclk -min 0.500 [get_ports tx_axis_tdata*]
set_output_delay -clock tx_axis_aclk -max 1.000 [get_ports tx_axis_tvalid]
set_output_delay -clock tx_axis_aclk -max 1.000 [get_ports tx_axis_tkeep*]
set_output_delay -clock tx_axis_aclk -max 1.000 [get_ports tx_axis_tlast]

# Input delays for AXI-Stream RX
set_input_delay -clock rx_axis_aclk -max 2.000 [get_ports rx_axis_tdata*]
set_input_delay -clock rx_axis_aclk -max 2.000 [get_ports rx_axis_tvalid]
set_input_delay -clock rx_axis_aclk -max 2.000 [get_ports rx_axis_tkeep*]
set_input_delay -clock rx_axis_aclk -max 2.000 [get_ports rx_axis_tlast]

# I2S interface delays
set_output_delay -clock i2s_bclk -max 3.000 [get_ports i2s_dout]
set_output_delay -clock i2s_bclk -min 1.000 [get_ports i2s_dout]
set_input_delay -clock i2s_bclk -max 3.000 [get_ports i2s_din]
set_input_delay -clock i2s_bclk -min 1.000 [get_ports i2s_din]
set_output_delay -clock i2s_bclk -max 2.000 [get_ports i2s_bclk_o]
set_output_delay -clock i2s_bclk -max 2.000 [get_ports i2s_lrclk_o]

# TDM interface delays
set_output_delay -clock tdm_bclk -max 3.000 [get_ports tdm_dout*]
set_output_delay -clock tdm_bclk -min 1.000 [get_ports tdm_dout*]
set_input_delay -clock tdm_bclk -max 3.000 [get_ports tdm_din*]
set_input_delay -clock tdm_bclk -min 1.000 [get_ports tdm_din*]
set_output_delay -clock tdm_bclk -max 2.000 [get_ports tdm_bclk_o]
set_output_delay -clock tdm_bclk -max 2.000 [get_ports tdm_fs_o]

# PDM interface delays
set_input_delay -clock pdm_clk -max 2.000 [get_ports pdm_din*]
set_input_delay -clock pdm_clk -min 1.000 [get_ports pdm_din*]
set_output_delay -clock pdm_clk -max 2.000 [get_ports pdm_lrsel]

# SPDIF interface delays
set_input_delay -clock audio_clk -max 5.000 [get_ports spdif_rx]
set_output_delay -clock audio_clk -max 5.000 [get_ports spdif_tx]

# Interrupt delay
set_output_delay -clock pclk -max 2.000 [get_ports irq]

###############################################################################
# SECTION 4: DRIVE/CAPACITANCE
###############################################################################

# Output drive strengths
set_driving_cell -lib_cell BUFFD2 -library standard_cell_lib \
    [get_ports prdata*]
set_driving_cell -lib_cell BUFFD2 -library standard_cell_lib \
    [get_ports pready]
set_driving_cell -lib_cell BUFFD2 -library standard_cell_lib \
    [get_ports tx_axis_tdata*]
set_driving_cell -lib_cell BUFFD2 -library standard_cell_lib \
    [get_ports tx_axis_tvalid]
set_driving_cell -lib_cell BUFFD2 -library standard_cell_lib \
    [get_ports tx_axis_tkeep*]
set_driving_cell -lib_cell BUFFD2 -library standard_cell_lib \
    [get_ports tx_axis_tlast]
set_driving_cell -lib_cell BUFFD2 -library standard_cell_lib \
    [get_ports i2s_dout]
set_driving_cell -lib_cell BUFFD2 -library standard_cell_lib \
    [get_ports i2s_bclk_o]
set_driving_cell -lib_cell BUFFD2 -library standard_cell_lib \
    [get_ports i2s_lrclk_o]
set_driving_cell -lib_cell BUFFD2 -library standard_cell_lib \
    [get_ports i2s_mclk]
set_driving_cell -lib_cell BUFFD2 -library standard_cell_lib \
    [get_ports tdm_dout*]
set_driving_cell -lib_cell BUFFD2 -library standard_cell_lib \
    [get_ports tdm_bclk_o]
set_driving_cell -lib_cell BUFFD2 -library standard_cell_lib \
    [get_ports tdm_fs_o]
set_driving_cell -lib_cell BUFFD2 -library standard_cell_lib \
    [get_ports pdm_lrsel]
set_driving_cell -lib_cell BUFFD2 -library standard_cell_lib \
    [get_ports spdif_tx]
set_driving_cell -lib_cell BUFFD2 -library standard_cell_lib \
    [get_ports irq]

# Input capacitance
set_load -pin_load 0.050 [get_ports pclk]
set_load -pin_load 0.050 [get_ports prst_n]
set_load -pin_load 0.050 [get_ports paddr*]
set_load -pin_load 0.050 [get_ports pwdata]
set_load -pin_load 0.050 [get_ports pwrite]
set_load -pin_load 0.050 [get_ports psel]
set_load -pin_load 0.050 [get_ports penable]

###############################################################################
# SECTION 5: TIMING EXCEPTIONS
###############################################################################

# False paths
set_false_path -from [get_ports psel] -to [get_ports pready]
set_false_path -from [get_ports penable] -to [get_ports pready]

# Multicycle paths
set_multicycle_path -setup 2 -from [get_ports paddr*] -to [get_ports prdata*]
set_multicycle_path -hold 1 -from [get_ports paddr*] -to [get_ports prdata*]

# Disable timing for asynchronous signals
set_false_path -from [get_ports prst_n]
set_false_path -from [get_ports rx_axis_rst_n]
set_false_path -from [get_ports tx_axis_rst_n]

###############################################################################
# SECTION 6: MAX DELAY
###############################################################################

set_max_delay -from [get_ports pclk] -to [get_registers *] 5.000
set_max_delay -from [get_registers *] -to [get_ports pclk] 5.000

###############################################################################
# SECTION 7: AREA CONSTRAINTS
###############################################################################

set_max_area 72000

###############################################################################
# SECTION 8: POWER CONSTRAINTS
###############################################################################

set_max_power -dynamic 0.083
set_max_leakage 0.002

###############################################################################
# SECTION 9: PORT CLASSIFICATION
###############################################################################

set_port_asynchronous -clock [get_clocks pclk] [get_ports prst_n]
set_port_asynchronous -clock [get_clocks tx_axis_aclk] [get_ports tx_axis_rst_n]
set_port_asynchronous -clock [get_clocks rx_axis_aclk] [get_ports rx_axis_rst_n]

###############################################################################
# SECTION 10: REGISTER GROUPING
###############################################################################

set_register_group -name audio_regfile [get_registers *audio_regfile*]
set_register_group -name i2s_controller [get_registers *i2s_controller*]
set_register_group -name tdm_controller [get_registers *tdm_controller*]
set_register_group -name pdm_controller [get_registers *pdm_controller*]
set_register_group -name spdif_controller [get_registers *spdif_controller*]
set_register_group -name audio_dsp [get_registers *audio_dsp*]
set_register_group -name volume_control [get_registers *volume_control*]
set_register_group -name sample_rate_converter [get_registers *sample_rate_converter*]

###############################################################################
# SECTION 11: DEBUG
###############################################################################

set timing_enable_multiple_clocks_per_reg true
set_analysis_type -setup -end default
set_analysis_type -hold -end default

###############################################################################
# END OF SDC FILE
###############################################################################
