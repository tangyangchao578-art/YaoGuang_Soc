# Set_false_path - PCI_Source Clocks
create_clock -period "250 MHz" [get_ports clk_sys] -name clk_sys
create_clock -period "500 MHz" [get_ports clk_phy] -name clk_phy

# Set_clock_groups - Asynchronous Clocks
set_clock_groups -asynchronous -group clk_sys -group clk_phy

# Input Delay Constraints
set_input_delay -clock clk_phy -max 0.5 [get_ports rx_data_p*]
set_input_delay -clock clk_phy -min 0.3 [get_ports rx_data_p*]
set_input_delay -clock clk_phy -max 0.5 [get_ports rx_data_n*]
set_input_delay -clock clk_phy -min 0.3 [get_ports rx_data_n*]
set_input_delay -clock clk_phy -max 0.5 [get_ports rx_clk_p]
set_input_delay -clock clk_phy -min 0.3 [get_ports rx_clk_p]
set_input_delay -clock clk_phy -max 0.5 [get_ports rx_clk_n]
set_input_delay -clock clk_phy -min 0.3 [get_ports rx_clk_n]

# Output Delay Constraints
set_output_delay -clock clk_phy -max 0.5 [get_ports tx_data_p*]
set_output_delay -clock clk_phy -min 0.3 [get_ports tx_data_p*]
set_output_delay -clock clk_phy -max 0.5 [get_ports tx_data_n*]
set_output_delay -clock clk_phy -min 0.3 [get_ports tx_data_n*]
set_output_delay -clock clk_phy -max 0.5 [get_ports tx_clk_p]
set_output_delay -clock clk_phy -min 0.3 [get_ports tx_clk_p]
set_output_delay -clock clk_phy -max 0.5 [get_ports tx_clk_n]
set_output_delay -clock clk_phy -min 0.3 [get_ports tx_clk_n]

# Set_max_delay - AXI Interface
set_max_delay -from [get_clocks clk_sys] -to [get_clocks clk_sys] 3.0
set_max_delay -from [get_ports axi_m_*] -to [get_ports axi_m_*] 3.0
set_max_delay -from [get_ports axi_s_*] -to [get_ports axi_s_*] 3.0

# Set_multicycle_path
set_multicycle_path -from [get_pins pcie_top/u_transaction_layer/axi_m_*] \
    -to [get_pins pcie_top/u_transaction_layer/axi_m_*] 2

# Set_false_path
set_false_path -from [get_ports rst_n*]
set_false_path -to [get_ports interrupt_out*]
set_false_path -from [get_ports link_training]
set_false_path -to [get_ports link_up]
set_false_path -to [get_ports link_width*]
set_false_path -to [get_ports link_rate*]
set_false_path -from [get_ports device_id*]
set_false_path -from [get_ports vendor_id*]
set_false_path -from [get_ports revision_id*]
set_false_path -from [get_ports class_code*]
set_false_path -from [get_ports msix_enable]
set_false_path -from [get_ports msi_enable]
set_false_path -from [get_ports power_state*]
set_false_path -to [get_ports error_*]

# Set_max_transition
set_max_transition 0.5 -clock clk_sys
set_max_transition 0.3 -clock clk_phy

# Set_max_capacitance
set_max_capacitance 50 -clock clk_sys
set_max_capacitance 30 -clock clk_phy

# Set_driving_cell
set_driving_cell -lib_cell INV_X4 -library standard_cells \
    [get_ports {axi_m_*, axi_s_*}]

set_driving_cell -lib_cell BUF_X8 -library standard_cells \
    [get_ports {tx_data_p*, tx_data_n*, tx_clk_p, tx_clk_n, tx_elec_idle}]

# Set_load
set_load -pin_load 0.5 [get_ports {tx_data_p*, tx_data_n*, tx_clk_p, tx_clk_n}]
set_load -pin_load 0.3 [get_ports {interrupt_out*, error_*}]

# Set_operating_conditions
set_operating_conditions -library typical -max ss_0p95v_125c

# Set_wire_load_model
set_wire_load_model -library typical -name test_bump

# Set_clock_uncertainty
set_clock_uncertainty -setup 0.1 [get_clocks clk_sys]
set_clock_uncertainty -hold 0.05 [get_clocks clk_sys]
set_clock_uncertainty -setup 0.1 [get_clocks clk_phy]
set_clock_uncertainty -hold 0.05 [get_clocks clk_phy]

# PCIe Specific Constraints
set_false_path -from [get_pins pcie_top/u_physical_layer/scrambler_state*]
set_false_path -from [get_pins pcie_top/u_data_link_layer/replay_buf*]
set_max_delay -from [get_pins pcie_top/u_transaction_layer/tl_*] \
    -to [get_pins pcie_top/u_data_link_layer/tl_*] 2.0
set_max_delay -from [get_pins pcie_top/u_data_link_layer/phy_*] \
    -to [get_pins pcie_top/u_physical_layer/phy_*] 1.0
set_max_delay -from [get_pins pcie_top/u_physical_layer/tx_*] \
    -to [get_ports tx_*] 1.0
set_max_delay -from [get_ports rx_*] \
    -to [get_pins pcie_top/u_physical_layer/rx_*] 1.0

# Lane-to-Lane Skew Constraints
set_max_delay -lane_to_lane 0.1 [get_ports {rx_data_p[*]}]
set_max_delay -lane_to_lane 0.1 [get_ports {tx_data_p[*]}]

# DLLP/TLP Processing Constraints
set_max_delay -from [get_pins pcie_top/u_transaction_layer/dll_*] \
    -to [get_pins pcie_top/u_data_link_layer/dll_*] 1.5
set_max_delay -from [get_pins pcie_top/u_data_link_layer/dll_*] \
    -to [get_pins pcie_top/u_transaction_layer/dll_*] 1.5

# Power Domain Constraints
set_power_domain -name PD_PCIE -primary_clock clk_phy \
    -primary_power_reset rst_n_phy

# IO Standard Constraints
set_io_standard -standard LVDS_25 [get_ports {tx_data_p*, tx_data_n*, rx_data_p*, rx_data_n*}]
set_io_standard -standard LVDS_25 [get_ports {tx_clk_p, tx_clk_n, rx_clk_p, rx_clk_n}]
set_io_standard -standard LVCMOS18 [get_ports {interrupt_out*, error_*, rst_n*}]
set_io_standard -standard LVCMOS18 [get_ports {axi_*}]

# DDR/SSI Constraints for PHY
set_ddr_address_cell -pin ADDR -library sram256x32
set_ddr_data_cell -pin DATA -library sram256x32

# Report Constraint Checks
report_constraint -all
