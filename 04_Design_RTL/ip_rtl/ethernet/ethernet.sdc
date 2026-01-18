# Set_false_path - Ethernet Source Clocks
create_clock -period "156.25 MHz" [get_ports clk_sys] -name clk_sys_10g
create_clock -period "125 MHz" [get_ports clk_sys] -name clk_sys_1g
create_clock -period "625 MHz" [get_ports clk_phy] -name clk_phy

# Set_clock_groups - Asynchronous Clocks
set_clock_groups -asynchronous -group clk_sys -group clk_phy

# XGMII Interface Constraints
set_input_delay -clock clk_phy -max 0.5 [get_ports xgmii_rx_clk]
set_input_delay -clock clk_phy -min 0.2 [get_ports xgmii_rx_clk]
set_input_delay -clock clk_phy -max 0.5 [get_ports xgmii_rx_ctl]
set_input_delay -clock clk_phy -max 0.5 [get_ports xgmii_rxd*]
set_output_delay -clock clk_phy -max 0.5 [get_ports xgmii_tx_clk]
set_output_delay -clock clk_phy -min 0.2 [get_ports xgmii_tx_clk]
set_output_delay -clock clk_phy -max 0.5 [get_ports xgmii_tx_ctl]
set_output_delay -clock clk_phy -max 0.5 [get_ports xgmii_txd*]

# RGMII Interface Constraints
set_input_delay -clock clk_phy -max 1.0 [get_ports rgmii_rx_clk]
set_input_delay -clock clk_phy -min 0.5 [get_ports rgmii_rx_clk]
set_input_delay -clock clk_phy -max 1.0 [get_ports rgmii_rx_ctl]
set_input_delay -clock clk_phy -max 1.0 [get_ports rgmii_rxd*]
set_output_delay -clock clk_phy -max 1.0 [get_ports rgmii_tx_clk]
set_output_delay -clock clk_phy -min 0.5 [get_ports rgmii_tx_clk]
set_output_delay -clock clk_phy -max 1.0 [get_ports rgmii_tx_ctl]
set_output_delay -clock clk_phy -max 1.0 [get_ports rgmii_txd*]

# GMII/MII Interface Constraints
set_input_delay -clock clk_phy -max 2.0 [get_ports phy_rx_clk]
set_input_delay -clock clk_phy -min 1.0 [get_ports phy_rx_clk]
set_input_delay -clock clk_phy -max 2.0 [get_ports phy_rx_dv]
set_input_delay -clock clk_phy -max 2.0 [get_ports phy_rx_err]
set_input_delay -clock clk_phy -max 2.0 [get_ports phy_rx_data*]
set_output_delay -clock clk_phy -max 2.0 [get_ports phy_tx_clk]
set_output_delay -clock clk_phy -min 1.0 [get_ports phy_tx_clk]
set_output_delay -clock clk_phy -max 2.0 [get_ports phy_tx_en]
set_output_delay -clock clk_phy -max 2.0 [get_ports phy_tx_err]
set_output_delay -clock clk_phy -max 2.0 [get_ports phy_tx_data*]

# AXI4-Stream Interface Constraints
set_max_delay -from [get_ports tx_axis_*] -to [get_pins ethernet_top/port_gen*/tx_axis_*] 2.0
set_max_delay -from [get_pins ethernet_top/port_gen*/rx_axis_*] -to [get_ports rx_axis_*] 2.0

# AXI4 DMA Interface Constraints
set_max_delay -from [get_clocks clk_sys] -to [get_clocks clk_sys] 4.0
set_max_delay -from [get_ports dma_*] -to [get_ports dma_*] 4.0

# Set_false_path
set_false_path -from [get_ports rst_n*]
set_false_path -to [get_ports eth_intr*]
set_false_path -from [get_ports phy_reset_n*]
set_false_path -from [get_ports link_status*]
set_false_path -from [get_ports link_speed*]
set_false_path -from [get_ports duplex_mode*]

# Set_max_transition
set_max_transition 0.3 -clock clk_sys
set_max_transition 0.2 -clock clk_phy

# Set_max_capacitance
set_max_capacitance 50 -clock clk_sys
set_max_capacitance 30 -clock clk_phy

# Set_driving_cell
set_driving_cell -lib_cell INV_X4 -library standard_cells \
    [get_ports {s_axibus_*, dma_*, eth_intr*}]

set_driving_cell -lib_cell BUF_X8 -library standard_cells \
    [get_ports {xgmii_*, rgmii_*, phy_*, tx_axis_*, rx_axis_*}]

# Set_load
set_load -pin_load 0.5 [get_ports {xgmii_*, rgmii_*, phy_*}]
set_load -pin_load 0.3 [get_ports {tx_axis_*, rx_axis_*, eth_intr*}]

# IO Standard Constraints
set_io_standard -standard LVDS_25 [get_ports {xgmii_*, rgmii_*}]
set_io_standard -standard LVCMOS18 [get_ports {phy_*, eth_intr*, rst_n*}]
set_io_standard -standard LVCMOS18 [get_ports {s_axibus_*, dma_*}]
set_io_standard -standard LVCMOS18 [get_ports {tx_axis_*, rx_axis_*}]

# Clock Constraints
set_clock_uncertainty -setup 0.1 [get_clocks clk_sys]
set_clock_uncertainty -hold 0.05 [get_clocks clk_sys]
set_clock_uncertainty -setup 0.05 [get_clocks clk_phy]
set_clock_uncertainty -hold 0.02 [get_clocks clk_phy]

# Multi-Port Constraints
set_max_delay -from [get_ports eth_intr*] \
    -to [get_pins ethernet_top/port_gen*/eth_intr*] 2.0

# TSN Specific Constraints
set_false_path -from [get_pins frame_preprocessor*/local_time*]
set_false_path -from [get_pins frame_preprocessor*/tsm_*]

# Report Constraints
report_constraint -all
