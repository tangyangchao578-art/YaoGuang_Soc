#===========================================
# CPU Cluster SDC Constraint File
#===========================================
# YaoGuang SoC - CPU Cluster
# Version: 1.0
# Author: Frontend Design Engineer
# Date: 2026-01-19
#===========================================

#===========================================
# 1. Clock Definitions
#===========================================

# A78AE Primary Clock (2.0 GHz target)
create_clock -name clk_a78ae_pclk -period 0.5 [get_ports clk_a78ae_pclk]
set_clock_groups -asynchronous -group clk_a78ae_pclk

# A78AE Secondary Clock (for L2 cache)
create_clock -name clk_a78ae_sclk -period 0.5 [get_ports clk_a78ae_sclk]
set_clock_groups -asynchronous -group clk_a78ae_sclk

# R52 Primary Clock (1.5 GHz target)
create_clock -name clk_r52_pclk -period 0.667 [get_ports clk_r52_pclk]
set_clock_groups -asynchronous -group clk_r52_pclk

# R52 Secondary Clock
create_clock -name clk_r52_sclk -period 0.667 [get_ports clk_r52_sclk]
set_clock_groups -asynchronous -group clk_r52_sclk

# Debug Clock
create_clock -name clk_debug -period 4.0 [get_ports clk_debug]
set_clock_groups -asynchronous -group clk_debug

# Scan Clock
create_clock -name clk_scan -period 2.0 [get_ports scan_clk]

#===========================================
# 2. Clock Transition / Uncertainty
#===========================================

set_clock_transition -rise -min 0.05 [get_clocks clk_a78ae_pclk]
set_clock_transition -rise -max 0.1 [get_clocks clk_a78ae_pclk]
set_clock_transition -fall -min 0.05 [get_clocks clk_a78ae_pclk]
set_clock_transition -fall -max 0.1 [get_clocks clk_a78ae_pclk]

set_clock_transition -rise -min 0.05 [get_clocks clk_r52_pclk]
set_clock_transition -rise -max 0.1 [get_clocks clk_r52_pclk]
set_clock_transition -fall -min 0.05 [get_clocks clk_r52_pclk]
set_clock_transition -fall -max 0.1 [get_clocks clk_r52_pclk]

# Clock uncertainty (setup)
set_clock_uncertainty -setup 0.1 [get_clocks clk_a78ae_pclk]
set_clock_uncertainty -setup 0.1 [get_clocks clk_r52_pclk]

# Clock uncertainty (hold)
set_clock_uncertainty -hold 0.05 [get_clocks clk_a78ae_pclk]
set_clock_uncertainty -hold 0.05 [get_clocks clk_r52_pclk]

#===========================================
# 3. Input Delay Constraints
#===========================================

# ACE Interface Input Delays (A78AE)
set_input_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_awready]
set_input_delay -clock clk_a78ae_pclk -fall 0.2 -max [get_ports ace_a78ae_awready]
set_input_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_wready]
set_input_delay -clock clk_a78ae_pclk -fall 0.2 -max [get_ports ace_a78ae_wready]
set_input_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_bresp*]
set_input_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_bid*]
set_input_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_bvalid]
set_input_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_arready]
set_input_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_rdata*]
set_input_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_rresp*]
set_input_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_rid*]
set_input_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_rlast]
set_input_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_rvalid]

# Snoop Channel Input Delays
set_input_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_awsnoop*]
set_input_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_awdomain*]
set_input_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_awparity]
set_input_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_crresp*]
set_input_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_crid*]
set_input_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_crvalid]
set_input_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_cdready]

# AXI Interface Input Delays (R52)
set_input_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_awready]
set_input_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_wready]
set_input_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_bresp*]
set_input_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_bid*]
set_input_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_bvalid]
set_input_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_arready]
set_input_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_rdata*]
set_input_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_rresp*]
set_input_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_rid*]
set_input_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_rlast]
set_input_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_rvalid]

# Interrupt Inputs
set_input_delay -clock clk_a78ae_pclk -rise 0.3 -max [get_ports irq_a78ae_ext*]
set_input_delay -clock clk_r52_pclk -rise 0.3 -max [get_ports irq_r52_ext*]

# Debug Inputs
set_input_delay -clock clk_debug -rise 0.5 -max [get_ports dbg_dap_*]
set_input_delay -clock clk_a78ae_pclk -rise 0.3 -max [get_ports dbg_trig_in_a78ae*]
set_input_delay -clock clk_r52_pclk -rise 0.3 -max [get_ports dbg_trig_in_r52*]

# Power Management Inputs
set_input_delay -clock clk_a78ae_pclk -rise 0.3 -max [get_ports pwr_a78ae_req*]
set_input_delay -clock clk_r52_pclk -rise 0.3 -max [get_ports pwr_r52_req*]

# Security Inputs
set_input_delay -clock clk_a78ae_pclk -rise 0.3 -max [get_ports sec_req*]
set_input_delay -clock clk_a78ae_pclk -rise 0.5 -max [get_ports sec_key*]

# DFT Inputs
set_input_delay -clock clk_scan -rise 0.2 -max [get_ports scan_enable]

#===========================================
# 4. Output Delay Constraints
#===========================================

# ACE Interface Output Delays (A78AE)
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_awid*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_awaddr*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_awlen*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_awsize*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_awburst*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_awlock]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_awcache*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_awprot*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_awqos*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_awregion*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_awuser*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_awvalid]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_wdata*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_wstrb*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_wlast]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_wuser*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_wvalid]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_bready]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_arid*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_araddr*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_arlen*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_arsize*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_arburst*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_arlock]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_arcache*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_arprot*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_arqos*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_arregion*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_aruser*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_arvalid]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_rready]

# Snoop Channel Output Delays
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_acsnoop*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_acdomain*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_acparity]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_crready]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_cddata*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_cdwstrb*]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_cdlast]
set_output_delay -clock clk_a78ae_pclk -rise 0.2 -max [get_ports ace_a78ae_cdvalid]

# AXI Interface Output Delays (R52)
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_awid*]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_awaddr*]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_awlen*]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_awsize*]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_awburst*]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_awlock]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_awcache*]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_awprot*]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_awqos*]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_awvalid]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_wdata*]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_wstrb*]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_wlast]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_wvalid]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_bready]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_arid*]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_araddr*]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_arlen*]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_arsize*]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_arburst*]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_arlock]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_arcache*]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_arprot*]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_arqos*]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_arvalid]
set_output_delay -clock clk_r52_pclk -rise 0.2 -max [get_ports axi_r52_rready]

# Interrupt Outputs
set_output_delay -clock clk_a78ae_pclk -rise 0.3 -max [get_ports irq_a78ae_to_pic*]
set_output_delay -clock clk_r52_pclk -rise 0.3 -max [get_ports irq_r52_to_pic*]
set_output_delay -clock clk_a78ae_pclk -rise 0.3 -max [get_ports timer_irq_a78ae*]
set_output_delay -clock clk_r52_pclk -rise 0.3 -max [get_ports timer_irq_r52*]

# GIC SPI Outputs
set_output_delay -clock clk_a78ae_pclk -rise 0.3 -max [get_ports gic_spi_target*]
set_output_delay -clock clk_a78ae_pclk -rise 0.3 -max [get_ports gic_spi_id*]
set_output_delay -clock clk_a78ae_pclk -rise 0.3 -max [get_ports gic_spi_valid]

# Debug Outputs
set_output_delay -clock clk_a78ae_pclk -rise 0.3 -max [get_ports dbg_trig_a78ae*]
set_output_delay -clock clk_r52_pclk -rise 0.3 -max [get_ports dbg_trig_r52*]
set_output_delay -clock clk_a78ae_pclk -rise 0.3 -max [get_ports trace_a78ae*]
set_output_delay -clock clk_a78ae_pclk -rise 0.3 -max [get_ports trace_a78ae_valid]
set_output_delay -clock clk_r52_pclk -rise 0.3 -max [get_ports trace_r52*]
set_output_delay -clock clk_r52_pclk -rise 0.3 -max [get_ports trace_r52_valid]
set_output_delay -clock clk_debug -rise 0.5 -max [get_ports dbg_dap_rdata*]
set_output_delay -clock clk_debug -rise 0.5 -max [get_ports dbg_dap_ack]

# Power Management Outputs
set_output_delay -clock clk_a78ae_pclk -rise 0.3 -max [get_ports pwr_a78ae_ack*]
set_output_delay -clock clk_a78ae_pclk -rise 0.3 -max [get_ports pwr_a78ae_status*]
set_output_delay -clock clk_r52_pclk -rise 0.3 -max [get_ports pwr_r52_ack*]
set_output_delay -clock clk_r52_pclk -rise 0.3 -max [get_ports pwr_r52_status*]

# Error Outputs
set_output_delay -clock clk_a78ae_pclk -rise 0.3 -max [get_ports error_a78ae*]
set_output_delay -clock clk_a78ae_pclk -rise 0.3 -max [get_ports error_a78ae_valid]
set_output_delay -clock clk_r52_pclk -rise 0.3 -max [get_ports error_r52*]
set_output_delay -clock clk_r52_pclk -rise 0.3 -max [get_ports error_r52_valid]

# Security Outputs
set_output_delay -clock clk_a78ae_pclk -rise 0.3 -max [get_ports sec_ack*]

#===========================================
# 5. Reset Constraints
#===========================================

set_false_path -from [get_ports rst_n_*]
set_max_delay -reset -reset_path 1.0 [get_ports rst_n_*]

#===========================================
# 6. Multi-Cycle Path Constraints
#===========================================

# AXI/ACE handshake can take multiple cycles
set_multicycle_path -setup -from [get_cells -hierarchical -filter {name =~ *axi*awvalid*}] -to [get_cells -hierarchical -filter {name =~ *axi*awready*}] 2
set_multicycle_path -hold -from [get_cells -hierarchical -filter {name =~ *axi*awvalid*}] -to [get_cells -hierarchical -filter {name =~ *axi*awready*}] 1

set_multicycle_path -setup -from [get_cells -hierarchical -filter {name =~ *axi*arvalid*}] -to [get_cells -hierarchical -filter {name =~ *axi*arready*}] 2
set_multicycle_path -hold -from [get_cells -hierarchical -filter {name =~ *axi*arvalid*}] -to [get_cells -hierarchical -filter {name =~ *axi*arready*}] 1

#===========================================
# 7. False Path Constraints
//===========================================

# Clock domain crossings (handled by synchronizers)
set_false_path -from [get_clocks clk_a78ae_pclk] -to [get_clocks clk_r52_pclk]
set_false_path -from [get_clocks clk_r52_pclk] -to [get_clocks clk_a78ae_pclk]
set_false_path -from [get_clocks clk_a78ae_pclk] -to [get_clocks clk_debug]
set_false_path -from [get_clocks clk_debug] -to [get_clocks clk_a78ae_pclk]
set_false_path -from [get_clocks clk_r52_pclk] -to [get_clocks clk_debug]
set_false_path -from [get_clocks clk_debug] -to [get_clocks clk_r52_pclk]

# DFT paths
set_false_path -from [get_ports scan_enable]
set_false_path -from [get_ports scan_clk]
set_false_path -from [get_ports mbist_enable]
set_false_path -to [get_ports mbist_done]
set_false_path -to [get_ports mbist_fail*]
set_false_path -from [get_ports atpg_mode]

#===========================================
# 8. Maximum Capacitance Constraints
//===========================================

set_max_capacitance 0.5 [get_ports -filter {direction == out}]
set_max_capacitance 0.2 [get_pins -filter {direction == out} -of [get_cells]]

#===========================================
# 9. Maximum Transition Constraints
//===========================================

set_max_transition 0.2 [get_ports -filter {direction == out}]
set_max_transition 0.1 [get_pins -filter {direction == out} -of [get_cells]]

#===========================================
# 10. Drive Strength Constraints
//===========================================

set_drive 1.0 [get_ports -filter {direction == out && name !~ rst_n*}]
set_drive 2.0 [get_ports rst_n_*]

#===========================================
# 11. Load Constraints
//===========================================

set_load -pin_load 0.05 [get_ports ace_a78ae_*]
set_load -pin_load 0.05 [get_ports axi_r52_*]
set_load -pin_load 0.02 [get_ports irq_*]
set_load -pin_load 0.02 [get_ports timer_irq_*]
set_load -pin_load 0.02 [get_ports gic_spi_*]

#===========================================
# 12. Area Constraints
//===========================================

set_max_area 24.0

#===========================================
# 13. Timing Exceptions for CDC
//===========================================

# Synchronizer chains for CDC (2-FF synchronizers)
set_false_path -through [get_cells -hierarchical -filter {name =~ *sync*ff*}]

#===========================================
# 14. Critical Path Groups
//===========================================

group_path -name A78AE_CLOCK -critical_range 0.1 [get_clocks clk_a78ae_pclk]
group_path -name R52_CLOCK -critical_range 0.1 [get_clocks clk_r52_pclk]

#===========================================
# 15. Report Settings
//===========================================

report_timing -delay_type max -max_paths 10 -significant_digits 3
report_constraint -all_violators
