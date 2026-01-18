#-----------------------------------------------------------------------------
# PMU SDC Constraints
# YaoGuang SoC - Power Management Unit
#-----------------------------------------------------------------------------

# Version: 1.0
# Date: 2026-01-19
#-----------------------------------------------------------------------------

#==============================================================================
# 1. Clock Constraints
#==============================================================================

# APB Clock (Primary control interface)
create_clock -name pmu_pclk -period 10.0 [get_ports pclk]

# Fast Clock (Power control logic)
create_clock -name pmu_clk_fast -period 5.0 [get_ports clk_fast]

# Slow Clock (Monitoring and sleep control)
create_clock -name pmu_clk_slow -period 100.0 [get_ports clk_slow]

# Derived Clock Groups
set_clock_groups -asynchronous -group {pmu_pclk} -group {pmu_clk_fast pmu_clk_slow}
set_clock_groups -asynchronous -group {pmu_clk_fast} -group {pmu_clk_slow}

#==============================================================================
# 2. Input Delay Constraints
#==============================================================================

# APB Interface Input Delays
set_input_delay -clock pmu_pclk -max 3.0 [get_ports paddr*]
set_input_delay -clock pmu_pclk -max 1.0 [get_ports pwrite]
set_input_delay -clock pmu_pclk -max 1.0 [get_ports penable]
set_input_delay -clock pmu_pclk -max 1.0 [get_ports pwdata*]
set_input_delay -clock pmu_pclk -max 1.0 [get_ports pstrb*]

# Monitor Input Delays
set_input_delay -clock pmu_clk_slow -max 20.0 [get_ports vmon_valid*]
set_input_delay -clock pmu_clk_slow -max 20.0 [get_ports vmon_data*]
set_input_delay -clock pmu_clk_slow -max 20.0 [get_ports tmon_valid*]
set_input_delay -clock pmu_clk_slow -max 20.0 [get_ports tmon_data*]
set_input_delay -clock pmu_clk_slow -max 20.0 [get_ports imon_valid*]
set_input_delay -clock pmu_clk_slow -max 20.0 [get_ports imon_data*]

# Wake-up Input Delays
set_input_delay -clock pmu_clk_slow -max 50.0 [get_ports wake_*]
set_input_delay -clock pmu_clk_slow -max 50.0 [get_ports por_n]

# Voltage Regulator Status
set_input_delay -clock pmu_clk_fast -max 10.0 [get_ports vreg_status*]

#==============================================================================
# 3. Output Delay Constraints
#==============================================================================

# APB Interface Output Delays
set_output_delay -clock pmu_pclk -max 4.0 [get_ports prdata*]
set_output_delay -clock pmu_pclk -max 2.0 [get_ports pslverr]

# Power Domain Control Outputs (Critical timing)
set_output_delay -clock pmu_clk_fast -max 2.0 [get_ports pd_enable*]
set_output_delay -clock pmu_clk_fast -max 2.0 [get_ports pd_iso_n*]
set_output_delay -clock pmu_clk_fast -max 2.0 [get_ports pd_ret_n*]
set_output_delay -clock pmu_clk_fast -max 2.0 [get_ports pd_clk_gate*]

# Voltage Regulator Control
set_output_delay -clock pmu_clk_fast -max 5.0 [get_ports vreg_ctrl*]

# DVFS Control Outputs
set_output_delay -clock pmu_clk_fast -max 3.0 [get_ports dvfs_*_level]
set_output_delay -clock pmu_clk_fast -max 3.0 [get_ports dvfs_volt_ctrl*]

# Interrupt Outputs
set_output_delay -clock pmu_pclk -max 5.0 [get_ports irq_*]
set_output_delay -clock pmu_pclk -max 5.0 [get_ports pmu_*]

#==============================================================================
# 4. False Path Constraints
#==============================================================================

# Asynchronous reset paths (synchronized internally)
set_false_path -from [get_ports presetn] -to [all_registers]
set_false_path -from [get_ports rstn_fast] -to [all_registers]
set_false_path -from [get_ports rstn_slow] -to [all_registers]

# Wake-up inputs to control logic (asynchronous)
set_false_path -from [get_ports wake_*] -to [all_registers]

# Power-on reset paths
set_false_path -from [get_ports por_n] -to [all_registers]

# Monitor data paths (sampled synchronously)
set_false_path -from [get_ports vmon_data*] -to [all_registers]
set_false_path -from [get_ports tmon_data*] -to [all_registers]
set_false_path -from [get_ports imon_data*] -to [all_registers]

#==============================================================================
# 5. Multi-Cycle Path Constraints
#==============================================================================

# Power domain sequencing (allow multiple cycles)
set_multicycle_path -setup 10 -from [all_registers] -to [get_ports pd_enable*]
set_multicycle_path -hold 5 -from [all_registers] -to [get_ports pd_enable*]

# DVFS transitions (voltage/frequency change settling)
set_multicycle_path -setup 5 -from [all_registers] -to [get_ports dvfs_*_level]
set_multicycle_path -setup 10 -from [all_registers] -to [get_ports dvfs_volt_ctrl*]

# Power state machine transitions
set_multicycle_path -setup 20 -from [all_registers] -to [get_power_domain_outputs]

#==============================================================================
# 6. Clock Latency Constraints
#==============================================================================

# Add clock latency for external clocks
set_clock_latency -source -max 0.5 [get_clocks pmu_pclk]
set_clock_latency -source -max 0.5 [get_clocks pmu_clk_fast]
set_clock_latency -source -max 0.5 [get_clocks pmu_clk_slow]

#==============================================================================
# 7. Transition/Load Constraints
#==============================================================================

# Output transition times
set_output_transition -max 0.5 [get_ports pd_enable*]
set_output_transition -max 0.5 [get_ports pd_iso_n*]
set_output_transition -max 0.5 [get_ports pd_ret_n*]
set_output_transition -max 1.0 [get_ports vreg_ctrl*]

# Estimated output loads
set_load -pin_load 0.05 [get_ports pd_enable*]
set_load -pin_load 0.05 [get_ports pd_iso_n*]
set_load -pin_load 0.05 [get_ports pd_ret_n*]
set_load -pin_load 0.1 [get_ports vreg_ctrl*]

#==============================================================================
# 8. Maximum Fanout Constraints
#==============================================================================

# Control signals with high fanout
set_max_fanout 50 [get_ports pd_enable*]
set_max_fanout 50 [get_ports pd_iso_n*]
set_max_fanout 20 [get_ports vreg_ctrl*]

#==============================================================================
# 9. Area and Power Constraints
#==============================================================================

# Target area (estimated PMU size)
set_max_area 2.0

# Power optimization
set_power_analysis -mode average
set_opt_strategy -area

#==============================================================================
# 10. Design Rule Constraints
#==============================================================================

# Maximum transition time
set_max_transition 0.5 [current_design]

# Maximum capacitance
set_max_capacitance 0.1 [current_design]

#==============================================================================
# End of SDC Constraints
#==============================================================================
