#-----------------------------------------------------------------------------
# NPU Cluster SDC Constraints
# File: npu_cluster.sdc
# Description: Timing Constraints for NPU Cluster
#-----------------------------------------------------------------------------
# Target Process: 7nm FinFET
# Design Style: Synchronous with multiple clock domains
#-----------------------------------------------------------------------------

#=============================================================================
# Create Clocks
#=============================================================================

# Main NPU Cluster Clock (2.0 GHz target)
create_clock -name clk_npu -period 0.5 [get_ports clk_i]

# NoC Interface Clock (can be different)
create_clock -name clk_noc -period 1.0 [get_ports noc_clk_i]

#=============================================================================
# Clock Groups
#=============================================================================

# Asynchronous clock groups
set_clock_groups -asynchronous \
    -group {clk_npu} \
    -group {clk_noc}

#=============================================================================
# Input/Output Delays
#=============================================================================

# NoC Read Channel Input Delays
set_input_delay -clock clk_noc -max 0.4 [get_ports noc_rdata_i*]
set_input_delay -clock clk_noc -max 0.4 [get_ports noc_rvalid_i]
set_input_delay -clock clk_noc -max 0.3 [get_ports noc_arready_i]
set_input_delay -clock clk_noc -max 0.3 [get_ports noc_wready_i]
set_input_delay -clock clk_noc -max 0.3 [get_ports noc_awready_i]
set_input_delay -clock clk_noc -max 0.3 [get_ports noc_bvalid_i]
set_input_delay -clock clk_noc -max 0.3 [get_ports noc_bid_i]

# NoC Write Channel Output Delays
set_output_delay -clock clk_noc -max 0.4 [get_ports noc_rid_o*]
set_output_delay -clock clk_noc -max 0.4 [get_ports noc_araddr_o*]
set_output_delay -clock clk_noc -max 0.4 [get_ports noc_arvalid_o]
set_output_delay -clock clk_noc -max 0.4 [get_ports noc_wdata_o*]
set_output_delay -clock clk_noc -max 0.4 [get_ports noc_wstrb_o*]
set_output_delay -clock clk_noc -max 0.4 [get_ports noc_wvalid_o]
set_output_delay -clock clk_noc -max 0.4 [get_ports noc_awid_o*]
set_output_delay -clock clk_noc -max 0.4 [get_ports noc_awaddr_o*]
set_output_delay -clock clk_noc -max 0.4 [get_ports noc_awvalid_o]

# Control Interface Delays
set_input_delay  -clock clk_npu -max 0.3 [get_ports cfg_*]
set_output_delay -clock clk_npu -max 0.3 [get_ports cfg_status_o*]
set_output_delay -clock clk_npu -max 0.3 [get_ports intr_*]

#=============================================================================
# False Paths
#=============================================================================

# Reset signals are asynchronous
set_false_path -from [get_ports rst_ni]
set_false_path -to [get_ports rst_ni]

# Clock gate enable can arrive late
set_false_path -from [get_ports clk_gate_en_i]

# Interrupts are level-sensitive, can have some skew
set_false_path -to [get_ports intr_*]

#=============================================================================
# Multi-Cycle Paths
// Pipeline stages within NPU have 1 cycle latency
set_multicycle_path -setup -end -from [get_pins -hierarchical -filter {name =~ "*pipe*"}] 1
set_multicycle_path -hold -end -from [get_pins -hierarchical -filter {name =~ "*pipe*"}] 0

# MAC array accumulation paths
set_multicycle_path -setup -end -from [get_pins -hierarchical -filter {name =~ "*mac*"}] 4
set_multicycle_path -hold -end -from [get_pins -hierarchical -filter {name =~ "*mac*"}] 3

#=============================================================================
# Maximum Delay (False Path Exceptions)
#=============================================================================

# Reset to flip-flop paths
set_max_delay -from [get_ports rst_ni] 2.0
set_max_delay -to [get_pins -hierarchical -filter {name =~ "*rst*"}] 2.0

#=============================================================================
# Clock Uncertainty
//=============================================================================

set_clock_uncertainty -setup 0.05 clk_npu
set_clock_uncertainty -hold 0.02 clk_npu
set_clock_uncertainty -setup 0.08 clk_noc
set_clock_uncertainty -hold 0.03 clk_noc

#=============================================================================
# Transition/Drive Constraints
//=============================================================================

set_driving_cell -lib_cell INV_X2 [get_ports clk_i]
set_driving_cell -lib_cell INV_X2 [get_ports rst_ni]

# NoC interface ports
set_driving_cell -lib_cell BUF_X4 [get_ports noc_*]
set_load -lib_cell INV_X1 0.05 [get_ports noc_*]

# Control interface
set_driving_cell -lib_cell INV_X2 [get_ports cfg_*]
set_load -lib_cell INV_X1 0.02 [get_ports cfg_*]

# Interrupt ports (lower drive strength allowed)
set_driving_cell -lib_cell INV_X4 [get_ports intr_*]

#=============================================================================
# Area Constraints (Optional for Synthesis)
//=============================================================================

set_max_area 36.0

#=============================================================================
# Power Constraints
//=============================================================================

set_max_dynamic_power 25.0 {mW}

#=============================================================================
# Timing Exceptions for RAM Interfaces
//=============================================================================

# Weight SRAM interface
set_false_path -from [get_pins -hierarchical -filter {name =~ "*weight_sram*addr*"}] \
               -to [get_pins -hierarchical -filter {name =~ "*weight_sram*mem*"}]

set_false_path -from [get_pins -hierarchical -filter {name =~ "*weight_sram*wdata*"}] \
               -to [get_pins -hierarchical -filter {name =~ "*weight_sram*mem*"}]

set_false_path -from [get_pins -hierarchical -filter {name =~ "*weight_sram*mem*"}] \
               -to [get_pins -hierarchical -filter {name =~ "*weight_sram*rdata*"}]

# Activation SRAM interface
set_false_path -from [get_pins -hierarchical -filter {name =~ "*act_sram*addr*"}] \
               -to [get_pins -hierarchical -filter {name =~ "*act_sram*mem*"}]

set_false_path -from [get_pins -hierarchical -filter {name =~ "*act_sram*wdata*"}] \
               -to [get_pins -hierarchical -filter {name =~ "*act_sram*mem*"}]

set_false_path -from [get_pins -hierarchical -filter {name =~ "*act_sram*mem*"}] \
               -to [get_pins -hierarchical -filter {name =~ "*act_sram*rdata*"}]

# Output Buffer interface
set_false_path -from [get_pins -hierarchical -filter {name =~ "*out_sram*addr*"}] \
               -to [get_pins -hierarchical -filter {name =~ "*out_sram*mem*"}]

set_false_path -from [get_pins -hierarchical -filter {name =~ "*out_sram*wdata*"}] \
               -to [get_pins -hierarchical -filter {name =~ "*out_sram*mem*"}]

set_false_path -from [get_pins -hierarchical -filter {name =~ "*out_sram*mem*"}] \
               -to [get_pins -hierarchical -filter {name =~ "*out_sram*rdata*"}]

#=============================================================================
# Design Rule Checks (DRC)
//=============================================================================

set_max_fanout 32 [get_design]
set_max_transition 0.1 [get_design]
set_max_capacitance 0.5 [get_design]

#=============================================================================
# End of NPU Cluster SDC Constraints
#=============================================================================
