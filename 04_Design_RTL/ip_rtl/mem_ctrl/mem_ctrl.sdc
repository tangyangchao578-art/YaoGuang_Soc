#-----------------------------------------------------------------------------
# LPDDR5 Memory Controller SDC Timing Constraints
# YaoGuang SoC Project
#-----------------------------------------------------------------------------
# Description:
#   SDC file for LPDDR5 Memory Controller timing constraints
#   Based on LPDDR5 6400 MT/s specification
#-----------------------------------------------------------------------------
# Version: 1.0
# Date: 2026-01-18
#-----------------------------------------------------------------------------

#=======================
# 1. Clock Definitions
#=======================

# Controller clock (derived from PLL)
create_clock -name mem_ctrl_clk -period 1.5625 [get_ports clk_i]
# 1.5625 ns = 640 MHz = 6400 MT/s data rate (DDR, so 640 MHz clock)

# AXI interface clock (may be different from controller clock)
create_clock -name axi_clk -period 2.0 [get_ports clk_i]
# 2.0 ns = 500 MHz for AXI interface

# PHY interface clocks (DFI clock)
create_clock -name dfi_clk -period 1.5625 [get_pins u_phy_if/clk_i]
create_clock -name dfi_phy_clk -period 1.5625

#=======================
# 2. Clock Groups
#=======================

# AXI clock group (asynchronous to other clocks)
set_clock_groups -asynchronous \
    -group {mem_ctrl_clk} \
    -group {axi_clk}

# PHY interface clock relationships
set_clock_groups -asynchronous \
    -group {mem_ctrl_clk} \
    -group {dfi_clk}

#=======================
# 3. Input/Output Delays
#=======================

# DFI interface input delays (from PHY)
set_input_delay -clock dfi_clk -max 0.8 [get_ports dfi_dq_i]
set_input_delay -clock dfi_clk -min 0.2 [get_ports dfi_dq_i]
set_input_delay -clock dfi_clk -max 0.6 [get_ports dfi_dqs_i]
set_input_delay -clock dfi_clk -min 0.3 [get_ports dfi_dqs_i]
set_input_delay -clock dfi_clk -max 0.5 [get_ports dfi_dbi_i]
set_input_delay -clock dfi_clk -max 0.5 [get_ports dfi_status_i]

# DFI interface output delays (to PHY)
set_output_delay -clock dfi_clk -max 0.8 [get_ports dfi_dq_o]
set_output_delay -clock dfi_clk -min 0.2 [get_ports dfi_dq_o]
set_output_delay -clock dfi_clk -max 0.6 [get_ports dfi_dqs_o]
set_output_delay -clock dfi_clk -min 0.3 [get_ports dfi_dqs_o]
set_output_delay -clock dfi_clk -max 0.5 [get_ports dfi_dm_o]
set_output_delay -clock dfi_clk -max 0.5 [get_ports dfi_dbi_o]
set_output_delay -clock dfi_clk -max 0.4 [get_ports dfi_cmd_o]
set_output_delay -clock dfi_clk -max 0.3 [get_ports dfi_cs_o]
set_output_delay -clock dfi_clk -max 0.3 [get_ports dfi_ck_o]
set_output_delay -clock dfi_clk -max 0.3 [get_ports dfi_cke_o]
set_output_delay -clock dfi_clk -max 0.3 [get_ports dfi_odt_o]

# AXI interface input delays
set_input_delay -clock axi_clk -max 1.0 [get_ports s_axiqos_araddr_i*]
set_input_delay -clock axi_clk -max 1.0 [get_ports s_axiqos_awaddr_i*]
set_input_delay -clock axi_clk -max 0.8 [get_ports s_axiqos_awid_i*]
set_input_delay -clock axi_clk -max 0.8 [get_ports s_axiqos_wdata_i*]
set_input_delay -clock axi_clk -max 0.5 [get_ports s_axiqos_wstrb_i*]
set_input_delay -clock axi_clk -max 0.5 [get_ports s_axiqos_wlast_i]
set_input_delay -clock axi_clk -max 1.0 [get_ports s_axiqos_arvalid_i]
set_input_delay -clock axi_clk -max 1.0 [get_ports s_axiqos_awvalid_i]
set_input_delay -clock axi_clk -max 1.0 [get_ports s_axiqos_wvalid_i]
set_input_delay -clock axi_clk -max 0.5 [get_ports s_axiqos_rready_i]
set_input_delay -clock axi_clk -max 0.5 [get_ports s_axiqos_bready_i]

# AXI interface output delays
set_output_delay -clock axi_clk -max 1.0 [get_ports s_axiqos_arready_o]
set_output_delay -clock axi_clk -max 1.0 [get_ports s_axiqos_awready_o]
set_output_delay -clock axi_clk -max 1.0 [get_ports s_axiqos_wready_o]
set_output_delay -clock axi_clk -max 1.0 [get_ports s_axiqos_rvalid_o]
set_output_delay -clock axi_clk -max 1.0 [get_ports s_axiqos_rlast_o]
set_output_delay -clock axi_clk -max 1.0 [get_ports s_axiqos_bvalid_o]
set_output_delay -clock axi_clk -max 1.0 [get_ports s_axiqos_rid_o*]
set_output_delay -clock axi_clk -max 1.0 [get_ports s_axiqos_rdata_o*]
set_output_delay -clock axi_clk -max 1.0 [get_ports s_axiqos_rresp_o*]
set_output_delay -clock axi_clk -max 1.0 [get_ports s_axiqos_bid_o*]
set_output_delay -clock axi_clk -max 1.0 [get_ports s_axiqos_bresp_o*]

#=======================
# 4. False Paths
#=======================

# CSR interface timing (registered externally)
set_false_path -from [get_ports csr_*_i] -to [get_ports csr_*_o]

# Reset signals
set_false_path -from [get_ports rst_n_i]

# Initialization and training signals
set_false_path -from [get_ports init_done_i]
set_false_path -from [get_ports init_done_o]
set_false_path -from [get_ports dfi_training_o]

# Refresh request/acknowledge (handled by scheduler)
set_false_path -from [get_ports refresh_req_i] -to [get_ports refresh_ack_o]

# ECC error signals (asynchronous events)
set_false_path -from [get_ports ecc_error_o]
set_false_path -from [get_ports ecc_corrected_o]
set_false_path -from [get_ports ecc_err_cnt_o]

# ECC test mode signals
set_false_path -from [get_ports ecc_test_mode_i]
set_false_path -from [get_ports ecc_err_inj_i]
set_false_path -from [get_ports ecc_err_type_i]

# Debug and status signals
set_false_path -from [get_ports status_o]
set_false_path -from [get_ports debug_o]

#=======================
# 5. Multicycle Paths
#=======================

# Command scheduling allows some flexibility
set_multicycle_path -setup -from [get_pins u_AXI_slave/*] -to [get_pins u_scheduler/*] 2
set_multicycle_path -hold -from [get_pins u_AXI_slave/*] -to [get_pins u_scheduler/*] 1

# Command queue to scheduler
set_multicycle_path -setup -from [get_pins u_cmd_queue/*] -to [get_pins u_scheduler/*] 2
set_multicycle_path -hold -from [get_pins u_cmd_queue/*] -to [get_pins u_scheduler/*] 1

# PHY interface path (DFI timing handled separately)
set_multicycle_path -setup -from [get_pins u_scheduler/*] -to [get_pins u_phy_if/*] 2
set_multicycle_path -hold -from [get_pins u_scheduler/*] -to [get_pins u_phy_if/*] 1

#=======================
# 6. Max Delay Constraints
#=======================

# Critical path from AXI to command queue
set_max_delay -from [get_pins u_AXI_slave/cmd_queue_wr_data_o*] \
              -to [get_pins u_cmd_queue/wr_data_i*] 1.0

# Critical path from scheduler to PHY
set_max_delay -from [get_pins u_scheduler/sched_cmd_*_o] \
              -to [get_pins u_phy_if/sched_cmd_*_i] 1.0

# ECC path constraints
set_max_delay -from [get_pins u_ecc/write_data_o*] \
              -to [get_pins u_phy_if/write_data_i*] 0.8
set_max_delay -from [get_pins u_phy_if/read_data_o*] \
              -to [get_pins u_ecc/read_data_i*] 0.8

#=======================
# 7. Min Delay Constraints
#=======================

set_min_delay 0.2 -from [get_pins u_AXI_slave/cmd_queue_wr_data_o*] \
                  -to [get_pins u_cmd_queue/wr_data_i*]

#=======================
# 8. Clock Uncertainty
#=======================

set_clock_uncertainty -setup 0.2 [get_clocks mem_ctrl_clk]
set_clock_uncertainty -hold 0.1 [get_clocks mem_ctrl_clk]
set_clock_uncertainty -setup 0.15 [get_clocks axi_clk]
set_clock_uncertainty -hold 0.08 [get_clocks axi_clk]
set_clock_uncertainty -setup 0.2 [get_clocks dfi_clk]
set_clock_uncertainty -hold 0.1 [get_clocks dfi_clk]

#=======================
# 9. Transition Times
#=======================

set_driving_cell -lib_cell INV_X4 -from [get_ports clk_i]
set_load -pin_load 0.05 [get_ports dfi_dq_o*]
set_load -pin_load 0.05 [get_ports dfi_cmd_o*]
set_load -pin_load 0.03 [get_ports dfi_cs_o*]

#=======================
# 10. Operating Conditions
#=======================

set_operating_conditions -max ss0p81v125c -min ff0p99vn40c

#=======================
# 11. Wire Load Models
#=======================

set wire_load_mode enclosed
set wire_load_model -name YAOGUANG_SOC_10K

#=======================
# 12. Port Attributes
#=======================

# Critical input ports
set_input_transition 0.2 [get_ports clk_i]
set_input_transition 0.3 [get_ports rst_n_i]
set_input_transition 0.4 [get_ports init_done_i]

# Critical output ports
set_output_load 0.05 [get_ports dfi_dq_o*]
set_output_load 0.03 [get_ports dfi_cmd_o*]
set_output_load 0.02 [get_ports dfi_cs_o*]

#=======================
# 13. Design Rules
#=======================

set_max_fanout 10 [get_ports clk_i]
set_max_capacitance 0.5 [get_ports clk_i]
set_max_transition 0.5 [get_ports clk_i]

#=======================
# 14. ECC Specific Constraints
#=======================

# ECC encoder/decoder timing (1-2 cycle latency as per spec)
set_max_delay -from [get_pins u_ecc/write_data_o*] \
              -to [get_pins u_phy_if/write_data_i*] 1.5
set_max_delay -from [get_pins u_phy_if/read_data_o*] \
              -to [get_pins u_ecc/read_data_i*] 2.0

# ECC error signals (single cycle from detection)
set_max_delay 0.5 -from [get_pins u_ecc/error_o] \
               -to [get_ports ecc_error_o]
set_max_delay 0.5 -from [get_pins u_ecc/corrected_o] \
               -to [get_ports ecc_corrected_o]

#=======================
# End of SDC
#=======================
