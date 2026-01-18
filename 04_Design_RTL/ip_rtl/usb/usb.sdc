# Set_false_path - USB Source Clocks
create_clock -period "250 MHz" [get_ports clk_sys] -name clk_sys
create_clock -period "500 MHz" [get_ports clk_phy] -name clk_phy

# Set_clock_groups - Asynchronous Clocks
set_clock_groups -asynchronous -group clk_sys -group clk_phy

# USB 2.0 IO Constraints
set_input_delay -clock clk_phy -max 2.0 [get_ports usb2_rx_dp*]
set_input_delay -clock clk_phy -min 0.5 [get_ports usb2_rx_dp*]
set_input_delay -clock clk_phy -max 2.0 [get_ports usb2_rx_dn*]
set_input_delay -clock clk_phy -min 0.5 [get_ports usb2_rx_dn*]

set_output_delay -clock clk_phy -max 1.0 [get_ports usb2_tx_dp*]
set_output_delay -clock clk_phy -min 0.3 [get_ports usb2_tx_dn*]
set_output_delay -clock clk_phy -max 1.0 [get_ports usb2_tx_oe*]
set_output_delay -clock clk_phy -min 0.3 [get_ports usb2_tx_oe*]

# USB 3.0 IO Constraints (SerDes)
set_input_delay -clock clk_phy -max 0.5 [get_ports usb3_rx_p*]
set_input_delay -clock clk_phy -min 0.2 [get_ports usb3_rx_p*]
set_input_delay -clock clk_phy -max 0.5 [get_ports usb3_rx_n*]
set_input_delay -clock clk_phy -min 0.2 [get_ports usb3_rx_n*]

set_output_delay -clock clk_phy -max 0.5 [get_ports usb3_tx_p*]
set_output_delay -clock clk_phy -min 0.2 [get_ports usb3_tx_n*]
set_output_delay -clock clk_phy -max 0.5 [get_ports usb3_tx_elec_idle*]
set_output_delay -clock clk_phy -min 0.2 [get_ports usb3_tx_elec_idle*]

# Reference Clock Constraints
set_output_delay -clock clk_phy -max 0.1 [get_ports ref_clk_p]
set_output_delay -clock clk_phy -min -0.1 [get_ports ref_clk_p]
set_output_delay -clock clk_phy -max 0.1 [get_ports ref_clk_n]
set_output_delay -clock clk_phy -min -0.1 [get_ports ref_clk_n]

# AXI Interface Constraints
set_max_delay -from [get_clocks clk_sys] -to [get_clocks clk_sys] 4.0
set_max_delay -from [get_ports s_axibus_*] -to [get_ports s_axibus_*] 4.0

# Set_false_path
set_false_path -from [get_ports rst_n*]
set_false_path -to [get_ports usb_intr*]
set_false_path -to [get_ports usb_overcurrent]
set_false_path -from [get_ports runtime_suspend]
set_false_path -to [get_ports runtime_resume]
set_false_path -from [get_ports global_power_enable]
set_false_path -from [get_ports phy_ready]
set_false_path -from [get_ports phy_status*]

# Set_max_transition
set_max_transition 0.5 -clock clk_sys
set_max_transition 0.3 -clock clk_phy

# Set_max_capacitance
set_max_capacitance 50 -clock clk_sys
set_max_capacitance 30 -clock clk_phy

# Set_driving_cell
set_driving_cell -lib_cell INV_X4 -library standard_cells \
    [get_ports s_axibus_*]

set_driving_cell -lib_cell BUF_X8 -library standard_cells \
    [get_ports {usb2_tx_*, usb3_tx_*, ref_clk_*}]

# Set_load
set_load -pin_load 0.5 [get_ports {usb2_tx_*, usb3_tx_*, ref_clk_*}]
set_load -pin_load 0.3 [get_ports usb_intr*]

# IO Standard Constraints
set_io_standard -standard LVCMOS18 [get_ports {usb_intr*, rst_n*}]
set_io_standard -standard LVCMOS18 [get_ports {s_axibus_*}]
set_io_standard -standard LVDS_25 [get_ports {usb3_tx_*, usb3_rx_*, ref_clk_*}]
set_io_standard -standard LVCMOS18 [get_ports {usb2_*}]

# Clock Constraints
set_clock_uncertainty -setup 0.1 [get_clocks clk_sys]
set_clock_uncertainty -hold 0.05 [get_clocks clk_sys]
set_clock_uncertainty -setup 0.05 [get_clocks clk_phy]
set_clock_uncertainty -hold 0.02 [get_clocks clk_phy]

# Multi-Port Constraints
set_max_delay -from [get_ports usb_intr*] -to [get_pins usb_top/port_gen*/usb_intr*] 2.0

# Port Isolation Constraints
set_false_path -from [get_pins usb_top/port_gen*/port_*] \
    -to [get_pins usb_top/port_gen*/port_*]

# Report Constraints
report_constraint -all
