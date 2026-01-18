# I2C/SPI/GPIO Composite Controller SDC Constraints

# Created: 2026-01-19
# Target Process: TBD (28nm or 22nm FD-SOI)
# Clock Frequency: 200MHz (APB4), 100MHz (SPI), 50MHz (I2C)

###############################################################################
# Create Clocks
###############################################################################

# APB4 Interface Clock (primary)
create_clock -name clk_apb -period 5.0 [get_ports clk_apb]

# SPI Core Clocks (per channel, up to 100MHz)
create_clock -name clk_spi -period 10.0 [get_ports clk_spi]
create_clock -name clk_spi_0 -period 10.0 [get_ports clk_spi_0]
create_clock -name clk_spi_1 -period 10.0 [get_ports clk_spi_1]
create_clock -name clk_spi_2 -period 10.0 [get_ports clk_spi_2]
create_clock -name clk_spi_3 -period 10.0 [get_ports clk_spi_3]

# I2C Core Clocks (per channel, up to 1MHz, divided from APB)
create_clock -name clk_i2c -period 1000.0 [get_ports clk_i2c]
create_clock -name clk_i2c_0 -period 1000.0 [get_ports clk_i2c_0]
create_clock -name clk_i2c_1 -period 1000.0 [get_ports clk_i2c_1]
create_clock -name clk_i2c_2 -period 1000.0 [get_ports clk_i2c_2]
create_clock -name clk_i2c_3 -period 1000.0 [get_ports clk_i2c_3]

# GPIO Reference Clock
create_clock -name clk_gpio -period 20.0 [get_ports clk_gpio]

# Test Clock
create_clock -name clk_test -period 2.5 [get_ports clk_test]

###############################################################################
# Generated Clocks
###############################################################################

# I2C derived clocks (SCL generation)
create_generated_clock -name i2c_scl_0 \
    -source [get_ports clk_apb] \
    -divide_by 100 \
    [get_ports i2c_scl_0]

create_generated_clock -name i2c_scl_1 \
    -source [get_ports clk_apb] \
    -divide_by 100 \
    [get_ports i2c_scl_1]

create_generated_clock -name i2c_scl_2 \
    -source [get_ports clk_apb] \
    -divide_by 100 \
    [get_ports i2c_scl_2]

create_generated_clock -name i2c_scl_3 \
    -source [get_ports clk_apb] \
    -divide_by 100 \
    [get_ports i2c_scl_3]

# SPI derived clocks (SCK generation)
create_generated_clock -name spi_sck_0 \
    -source [get_ports clk_spi] \
    -edges {1 3 5} \
    [get_ports spi_sck_0]

create_generated_clock -name spi_sck_1 \
    -source [get_ports clk_spi] \
    -edges {1 3 5} \
    [get_ports spi_sck_1]

create_generated_clock -name spi_sck_2 \
    -source [get_ports clk_spi] \
    -edges {1 3 5} \
    [get_ports spi_sck_2]

create_generated_clock -name spi_sck_3 \
    -source [get_ports clk_spi] \
    -edges {1 3 5} \
    [get_ports spi_sck_3]

###############################################################################
# Clock Groups
###############################################################################

# Asynchronous clock domains
set_clock_groups -asynchronous \
    -group [get_clocks clk_apb] \
    -group [get_clocks clk_spi* -include_root_clocks] \
    -group [get_clocks clk_i2c* -include_root_clocks] \
    -group [get_clocks clk_gpio] \
    -group [get_clocks clk_test]

# I2C and APB can have timing relationship for register access
set_clock_groups -asynchronous \
    -group [get_clocks clk_i2c*] \
    -group [get_clocks clk_apb]

###############################################################################
# Input/Output Delays - APB4 Interface
###############################################################################

# APB4 Input Delays
set_input_delay -clock clk_apb -max 2.0 [get_ports paddr*]
set_input_delay -clock clk_apb -max 2.0 [get_ports pwrite]
set_input_delay -clock clk_apb -max 2.0 [get_ports pwdata*]
set_input_delay -clock clk_apb -max 2.0 [get_ports psel*]
set_input_delay -clock clk_apb -max 2.0 [get_ports penable]

set_input_delay -clock clk_apb -min 0.5 [get_ports paddr*]
set_input_delay -clock clk_apb -min 0.5 [get_ports pwrite]
set_input_delay -clock clk_apb -min 0.5 [get_ports pwdata*]
set_input_delay -clock clk_apb -min 0.5 [get_ports psel*]
set_input_delay -clock clk_apb -min 0.5 [get_ports penable]

# APB4 Output Delays
set_output_delay -clock clk_apb -max 4.0 [get_ports prdata*]
set_output_delay -clock clk_apb -max 4.0 [get_ports pready]
set_output_delay -clock clk_apb -max 4.0 [get_ports pslverr]
set_output_delay -clock clk_apb -min 0.5 [get_ports prdata*]
set_output_delay -clock clk_apb -min 0.5 [get_ports pready]
set_output_delay -clock clk_apb -min 0.5 [get_ports pslverr]

###############################################################################
# Input/Output Delays - SPI Interface
################################################################################################################################################

# SPI Output Delays (SCK to data)
set_output_delay -clock spi_sck_0 -max 4.0 [get_ports spi_mosi_0*]
set_output_delay -clock spi_sck_0 -min 1.0 [get_ports spi_mosi_0*]
set_output_delay -clock spi_sck_1 -max 4.0 [get_ports spi_mosi_1*]
set_output_delay -clock spi_sck_1 -min 1.0 [get_ports spi_mosi_1*]
set_output_delay -clock spi_sck_2 -max 4.0 [get_ports spi_mosi_2*]
set_output_delay -clock spi_sck_2 -min 1.0 [get_ports spi_mosi_2*]
set_output_delay -clock spi_sck_3 -max 4.0 [get_ports spi_mosi_3*]
set_output_delay -clock spi_sck_3 -min 1.0 [get_ports spi_mosi_3*]

# SPI Input Delays (SCK to data)
set_input_delay -clock spi_sck_0 -max 3.0 [get_ports spi_miso_0*]
set_input_delay -clock spi_sck_0 -min 1.0 [get_ports spi_miso_0*]
set_input_delay -clock spi_sck_1 -max 3.0 [get_ports spi_miso_1*]
set_input_delay -clock spi_sck_1 -min 1.0 [get_ports spi_miso_1*]
set_input_delay -clock spi_sck_2 -max 3.0 [get_ports spi_miso_2*]
set_input_delay -clock spi_sck_2 -min 1.0 [get_ports spi_miso_2*]
set_input_delay -clock spi_sck_3 -max 3.0 [get_ports spi_miso_3*]
set_input_delay -clock spi_sck_3 -min 1.0 [get_ports spi_miso_3*]

# SPI Chip Select Setup/Hold
set_output_delay -clock spi_sck_0 -max 2.0 [get_ports spi_cs_0*]
set_output_delay -clock spi_sck_0 -min -0.5 [get_ports spi_cs_0*]
set_output_delay -clock spi_sck_1 -max 2.0 [get_ports spi_cs_1*]
set_output_delay -clock spi_sck_1 -min -0.5 [get_ports spi_cs_1*]
set_output_delay -clock spi_sck_2 -max 2.0 [get_ports spi_cs_2*]
set_output_delay -clock spi_sck_2 -min -0.5 [get_ports spi_cs_2*]
set_output_delay -clock spi_sck_3 -max 2.0 [get_ports spi_cs_3*]
set_output_delay -clock spi_sck_3 -min -0.5 [get_ports spi_cs_3*]

###############################################################################
# Input/Output Delays - I2C Interface
###############################################################################

# I2C SDA/SCL (open-drain, bidirectional)
set_input_delay -clock i2c_scl_0 -max 200.0 [get_ports i2c_sda_0]
set_input_delay -clock i2c_scl_0 -min 50.0 [get_ports i2c_sda_0]
set_input_delay -clock i2c_scl_1 -max 200.0 [get_ports i2c_sda_1]
set_input_delay -clock i2c_scl_1 -min 50.0 [get_ports i2c_sda_1]
set_input_delay -clock i2c_scl_2 -max 200.0 [get_ports i2c_sda_2]
set_input_delay -clock i2c_scl_2 -min 50.0 [get_ports i2c_sda_2]
set_input_delay -clock i2c_scl_3 -max 200.0 [get_ports i2c_sda_3]
set_input_delay -clock i2c_scl_3 -min 50.0 [get_ports i2c_sda_3]

###############################################################################
# Input/Output Delays - GPIO Interface
###############################################################################

# GPIO Input Delays
set_input_delay -clock clk_gpio -max 2.0 [get_ports gpio_in*]
set_input_delay -clock clk_gpio -min 0.5 [get_ports gpio_in*]

# GPIO Output Delays
set_output_delay -clock clk_gpio -max 3.0 [get_ports gpio_out*]
set_output_delay -clock clk_gpio -min 0.5 [get_ports gpio_out*]

# GPIO Output Enable
set_output_delay -clock clk_gpio -max 3.0 [get_ports gpio_oe*]
set_output_delay -clock clk_gpio -min 0.5 [get_ports gpio_oe*]

###############################################################################
# False Paths
###############################################################################

# Reset paths
set_false_path -from [get_ports rst_n] -to [all_registers]
set_false_path -from [get_ports rst_apb_n] -to [all_registers]
set_false_path -from [get_ports rst_spi_n] -to [all_registers]
set_false_path -from [get_ports rst_i2c_n] -to [all_registers]
set_false_path -from [get_ports rst_gpio_n] -to [all_registers]

# Asynchronous reset release
set_false_path -from [get_ports arst_n] -to [all_registers -clock_nodes]

# Test mode paths
set_false_path -from [get_ports test_mode]
set_false_path -from [get_ports scan_enable]

# Open-drain I2C signals (timing not applicable)
set_false_path -from [get_ports i2c_sda_*] -to [get_ports i2c_sda_*]
set_false_path -from [get_ports i2c_scl_*] -to [get_ports i2c_scl_*]

###############################################################################
# Multicycle Paths
###############################################################################

# APB to register write path
set_multicycle_path -setup 2 -from [get_ports psel*] -to [get_registers *paddr_reg*]
set_multicycle_path -hold 1 -from [get_ports psel*] -to [get_registers *paddr_reg*]

# Register to APB read path
set_multicycle_path -setup 1 -from [get_registers *prdata*] -to [get_ports prdata*]
set_multicycle_path -hold 0 -from [get_registers *prdata*] -to [get_ports prdata*]

# I2C to APB domain crossing
set_multicycle_path -setup 4 -from [get_clocks clk_i2c*] -to [get_clocks clk_apb]
set_multicycle_path -hold 3 -from [get_clocks clk_i2c*] -to [get_clocks clk_apb]

###############################################################################
# Maximum Delay Constraints
###############################################################################

# Reset to registers
set_max_delay 10.0 -from [get_ports rst_n] -to [all_registers]
set_max_delay 10.0 -from [get_ports rst_apb_n] -to [all_registers]

# Clock domain crossing paths
set_max_delay -from [get_clocks clk_apb] -to [get_clocks clk_spi*] 20.0
set_max_delay -from [get_clocks clk_spi*] -to [get_clocks clk_apb] 20.0
set_max_delay -from [get_clocks clk_apb] -to [get_clocks clk_i2c*] 50.0
set_max_delay -from [get_clocks clk_i2c*] -to [get_clocks clk_apb] 50.0
set_max_delay -from [get_clocks clk_apb] -to [get_clocks clk_gpio] 10.0
set_max_delay -from [get_clocks clk_gpio] -to [get_clocks clk_apb] 10.0

###############################################################################
# Driving Cells / Load Constraints
###############################################################################

# SPI Output driving strength (stronger for high-speed)
set_driving_cell -lib_cell BUF_X4 -library standard_cells [get_ports spi_mosi*]
set_driving_cell -lib_cell BUF_X4 -library standard_cells [get_ports spi_sck*]
set_driving_cell -lib_cell BUF_X4 -library standard_cells [get_ports spi_cs*]

# I2C Output (open-drain, weak driver)
set_driving_cell -lib_cell NAND2_X1 -library standard_cells [get_ports i2c_sda_*]
set_driving_cell -lib_cell NAND2_X1 -library standard_cells [get_ports i2c_scl_*]

# GPIO Output
set_driving_cell -lib_cell BUF_X4 -library standard_cells [get_ports gpio_out*]
set_driving_cell -lib_cell BUF_X4 -library standard_cells [get_ports gpio_oe*]

# APB Output
set_driving_cell -lib_cell BUF_X4 -library standard_cells [get_ports prdata*]
set_driving_cell -lib_cell BUF_X4 -library standard_cells [get_ports pready]
set_driving_cell -lib_cell BUF_X4 -library standard_cells [get_ports interrupt*]

# Input transition times
set_input_transition -min 0.05 -library standard_cells [get_ports spi_miso*]
set_input_transition -max 0.2 -library standard_cells [get_ports spi_miso*]
set_input_transition -min 0.05 -library standard_cells [get_ports gpio_in*]
set_input_transition -max 0.2 -library standard_cells [get_ports gpio_in*]

# Output loads
set_load -pin_load 0.05 [get_ports spi_mosi*]
set_load -pin_load 0.05 [get_ports spi_sck*]
set_load -pin_load 0.05 [get_ports spi_cs*]
set_load -pin_load 0.1 [get_ports gpio_out*]
set_load -pin_load 0.1 [get_ports gpio_oe*]
set_load -pin_load 0.05 [get_ports interrupt*]

###############################################################################
# Clock Latency
###############################################################################

set_clock_latency -source -max 0.5 [get_clocks clk_spi]
set_clock_latency -source -min 0.2 [get_clocks clk_spi]
set_clock_latency -max 0.3 [get_clocks clk_spi]
set_clock_latency -min 0.1 [get_clocks clk_spi]

set_clock_latency -source -max 1.0 [get_clocks clk_i2c]
set_clock_latency -source -min 0.5 [get_clocks clk_i2c]
set_clock_latency -max 0.5 [get_clocks clk_i2c]
set_clock_latency -min 0.2 [get_clocks clk_i2c]

###############################################################################
# Clock Uncertainty
###############################################################################

set_clock_uncertainty -setup 0.2 [get_clocks clk_apb]
set_clock_uncertainty -hold 0.1 [get_clocks clk_apb]
set_clock_uncertainty -setup 0.15 [get_clocks clk_spi]
set_clock_uncertainty -hold 0.08 [get_clocks clk_spi]
set_clock_uncertainty -setup 0.1 [get_clocks clk_i2c]
set_clock_uncertainty -hold 0.05 [get_clocks clk_i2c]
set_clock_uncertainty -setup 0.1 [get_clocks clk_gpio]
set_clock_uncertainty -hold 0.05 [get_clocks clk_gpio]

###############################################################################
# Area Constraints
###############################################################################

# Target area for composite controller
set_max_area 300000  # ~300K um^2

# Sub-module area budgets
set_max_area -group i2c_controller_x4 80000
set_max_area -group spi_controller_x4 100000
set_max_area -group gpio_128bit 60000
set_max_area -group interrupt_aggregator 20000
set_max_area -group apb_bridge 10000

###############################################################################
# Power Constraints
###############################################################################

set_max_dynamic_power 30 mW
set_max_leakage_power 3 mW

###############################################################################
# Timing Exceptions
###############################################################################

# FIFO paths
set_false_path -through [get_cells -hierarchical *fifo*]

# Async CDC paths
set_false_path -through [get_cells -hierarchical *async*]

# I2C glitch filter paths
set_false_path -through [get_cells -hierarchical *i2c*glitch*]

###############################################################################
# IO Standard
###############################################################################

set_io_standard -lib_cell LVTTL18 [get_ports clk_apb clk_spi clk_i2c clk_gpio rst_n*]
set_io_standard -lib_cell LVTTL18 [get_ports paddr* pwrite pwdata* psel* penable pready]
set_io_standard -lib_cell LVTTL18 [get_ports prdata* pslverr interrupt*]
set_io_standard -lib_cell LVTTL18 [get_ports spi_*]
set_io_standard -lib_cell LVTTL18 [get_ports i2c_*]
set_io_standard -lib_cell LVTTL18 [get_ports gpio_*]

###############################################################################
# DFT Constraints
###############################################################################

set_scan_configuration -chain_count 8

create_clock -name clk_scan -period 10.0 [get_ports clk_scan]

set_dft_signal -view existing_dft -type ScanClock -port clk_scan
set_dft_signal -view existing_dft -type Reset -port rst_n

###############################################################################
# Sign-off Corners
###############################################################################

set_operating_conditions -max tt_1p2v_125c
set_operating_conditions -min ss_1p0v_m40c
set_operating_conditions -typical ff_1p4v_m40c

###############################################################################
# End of SDC Constraints
###############################################################################
