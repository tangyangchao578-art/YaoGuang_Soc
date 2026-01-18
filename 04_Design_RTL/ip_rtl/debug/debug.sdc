# Debug Module SDC (Synopsys Design Constraints)
# YaoGuang SoC - Debug Subsystem
# Version: 1.0
# Date: 2026-01-18

#==============================================================================
# 1. Clock Definitions
#==============================================================================

# Primary debug clock (from system clock domain)
create_clock -name dbg_clk -period 5.0 [get_ports clk_i]
set_clock_uncertainty -setup 0.2 dbg_clk
set_clock_uncertainty -hold 0.1 dbg_clk

# JTAG TCK clock (async to system)
create_clock -name jtag_tck -period 50.0 [get_ports jtag_tck_i]
set_clock_uncertainty -setup 2.0 jtag_tck
set_clock_uncertainty -hold 1.0 jtag_tck

# SWD clock (async to system)
create_clock -name swd_clk -period 10.0 [get_ports swd_clk_i]
set_clock_uncertainty -setup 0.5 swd_clk
set_clock_uncertainty -hold 0.25 swd_clk

# Trace output clock
create_clock -name trace_clk -period 8.0 [get_ports trace_clk_o]
set_clock_uncertainty -setup 0.3 trace_clk
set_clock_uncertainty -hold 0.15 trace_clk

#==============================================================================
# 2. Clock Groups (Asynchronous)
#==============================================================================

set_clock_groups -asynchronous \
    -group {dbg_clk} \
    -group {jtag_tck} \
    -group {swd_clk} \
    -group {trace_clk}

#==============================================================================
# 3. Input/Output Delays
#==============================================================================

# JTAG inputs (registered at TAP)
set_input_delay -clock jtag_tck -max 5.0 [get_ports jtag_tms_i]
set_input_delay -clock jtag_tck -max 5.0 [get_ports jtag_tdi_i]
set_input_delay -clock jtag_tck -max 10.0 [get_ports jtag_trst_ni]

# SWD inputs
set_input_delay -clock swd_clk -max 2.0 [get_ports swd_clk_i]
set_input_delay -clock swd_clk -max 2.0 -add_delay [get_ports swd_io_b]

# Trace outputs (registered)
set_output_delay -clock trace_clk -max 2.0 [get_ports trace_data_o[*]]
set_output_delay -clock trace_clk -max 1.0 [get_ports trace_valid_o]
set_output_delay -clock trace_clk -max 1.0 [get_ports trace_sync_o]

# Debug control outputs
set_output_delay -clock dbg_clk -max 2.0 [get_ports cpu_halt_o[*]]
set_output_delay -clock dbg_clk -max 2.0 [get_ports dbg_ack_o]

#==============================================================================
# 4. Set False Paths
#==============================================================================

# JTAG/SWD reset paths (async reset)
set_false_path -from [get_ports jtag_trst_ni] -to [all_clocks]
set_false_path -from [get_ports rst_ni] -to [get_ports jtag_tdo_o]

# Debug request/ack handshake (handshake crossing clock domains)
set_false_path -from [get_ports dbg_req_i] -to [get_ports dbg_ack_o]

# Interrupt outputs (debug events)
set_false_path -from [all_registers -clock dbg_clk] -to [get_ports debug_int_o]
set_false_path -from [all_registers -clock dbg_clk] -to [get_ports breakpoint_o]
set_false_path -from [all_registers -clock dbg_clk] -to [get_ports watchpoint_o]

#==============================================================================
# 5. Multicycle Paths
#==============================================================================

# JTAG shift operations (data stable for multiple TCK cycles)
set_multicycle_path -setup -end -from [get_clocks jtag_tck] -to [get_clocks dbg_clk] 2
set_multicycle_path -hold -end -from [get_clocks jtag_tck] -to [get_clocks dbg_clk] 1

# DAP access (APB transaction takes multiple cycles)
set_multicycle_path -setup -from [get_clocks dbg_clk] -to [get_clocks dbg_clk] 3 \
    -through [get_pins -hierarchical -filter "name=~*apb_enable*"]
set_multicycle_path -hold -from [get_clocks dbg_clk] -to [get_clocks dbg_clk] 2 \
    -through [get_pins -hierarchical -filter "name=~*apb_enable*"]

# Trace buffer read (async FIFO read)
set_multicycle_path -setup -from [get_clocks dbg_clk] -to [get_clocks trace_clk] 1
set_multicycle_path -hold -from [get_clocks dbg_clk] -to [get_clocks trace_clk] 0

#==============================================================================
# 6. Maximum Delay Constraints
#==============================================================================

# JTAG TCK period (20 MHz max)
set_max_delay -from [get_ports jtag_tck_i] -to [get_ports jtag_tdo_o] 40.0

# SWD turnaround time
set_max_delay -from [get_ports swd_clk_i] -to [get_ports swd_io_b] 5.0

# Trace data valid before clock
set_max_delay -from [get_clocks trace_clk] -to [get_ports trace_data_o[*]] 3.0

#==============================================================================
# 7. Driving Cells (I/O Constraints)
#==============================================================================

# JTAG outputs (medium strength)
set_driving_cell -lib_cell BUFG \
    -from [get_clocks jtag_tck] \
    [get_ports jtag_tdo_o]

# SWD bidirectional (open-drain style)
set_drive 1.0 [get_ports swd_io_b]

# Trace outputs (high strength for long traces)
set_driving_cell -lib_cell OBUF \
    -from [get_clocks trace_clk] \
    [get_ports trace_data_o[*]]

set_driving_cell -lib_cell OBUF \
    -from [get_clocks trace_clk] \
    [get_ports trace_valid_o]

# Debug control outputs
set_driving_cell -lib_cell OBUF \
    [get_ports cpu_halt_o[*]]

set_driving_cell -lib_cell OBUF \
    [get_ports dbg_ack_o]

#==============================================================================
# 8. Load Constraints
#==============================================================================

# Estimate trace port capacitance
set_load -pin_load 5.0 [get_ports trace_data_o[*]]
set_load -pin_load 2.0 [get_ports trace_valid_o]
set_load -pin_load 2.0 [get_ports trace_sync_o]

# JTAG output load
set_load -pin_load 10.0 [get_ports jtag_tdo_o]

#==============================================================================
# 9. Area Constraints
#==============================================================================

# Maximum area for debug subsystem
set_max_area 1.2

#==============================================================================
# 10. Power Constraints
#==============================================================================

# Dynamic power target
set_max_dynamic_power 50.0 mW

# Static/leakage power target
set_max_leakage_power 5.0 mW

#==============================================================================
# 11. Timing Exceptions
#==============================================================================

# Disable timing on test mode
set_timing_ignore [get_ports test_mode_i]

# Register-to-register paths within async FIFOs have no timing constraints
set_false_path -through [get_pins -hierarchical -filter "name=~*fifo*rd_ptr*"]
set_false_path -through [get_pins -hierarchical -filter "name=~*fifo*wr_ptr*"]

#==============================================================================
# 12. Optimization Constraints
#==============================================================================

# Enable register retiming for performance
set_optimize_register -on

# Allow power-aware optimization
set_power_op_mode high_effort

# Enable timing-driven placement for high-speed paths
set_timing_driven_placement true

#==============================================================================
# 13. Module-Level Constraints (Debug Sub-modules)
#==============================================================================

# Trace buffer constraints
set_current_design debug_top
set_max_delay -from [get_pins u_trace_buffer/atvalid_i] \
              -to [get_pins u_trace_buffer/atready_o] 2.0

# DAP access path
set_max_delay -from [get_pins u_dap/apb_enable] \
              -to [get_pins u_dap/apb_ready] 5.0

# JTAG to DAP path
set_max_delay -from [get_pins u_jtag_controller/dr_valid_o] \
              -to [get_pins u_dap/jtag_dr_valid_i] 3.0

#==============================================================================
# 14. Report Settings
#==============================================================================

report_timing -delay_type max -max_paths 50 -nworst 10
report_clock -skew
report_constraint -all_violators
report_power -hierarchy

#==============================================================================
# End of SDC
#==============================================================================
