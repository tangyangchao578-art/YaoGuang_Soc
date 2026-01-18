###############################################################################
# YaoGuang SoC Palladium Emulation Compilation Script
# Level: CV Verification Architect
# Date: 2026-01-18
# Target: Synopsys Palladium Z1/Z2 Emulation System
###############################################################################

###############################################################################
# Compilation Configuration
###############################################################################

# Design root directory
set design_root "../../../../04_Design_RTL"
set rtl_dir "${design_root}/ip_rtl"
set soc_top_dir "${design_root}/soc_top"

# Output directories
set comp_dir "./compile"
set work_dir "./work"
set xmr_dir "./xmr"
set snapshot_dir "./snapshots"

# Emulation settings
set emu_platform "PALLADIUM_Z2"
set emu_clock_period 10.0
set emu_engines 8

###############################################################################
# Compile Design Sources
###############################################################################

proc compile_design {} {
    global design_root rtl_dir soc_top_dir comp_dir work_dir xmr_dir snapshot_dir
    global emu_platform emu_clock_period emu_engines
    
    puts "=========================================="
    puts "YaoGuang SoC Palladium Emulation Compiler"
    puts "=========================================="
    puts ""
    puts "Platform:     ${emu_platform}"
    puts "Clock Period: ${emu_clock_period} ns"
    puts "Engines:      ${emu_engines}"
    puts ""
    
    # Create directories
    file mkdir ${comp_dir}
    file mkdir ${work_dir}
    file mkdir ${xmr_dir}
    file mkdir ${snapshot_dir}
    
    # Initialize compilation
    init_compile -dir ${comp_dir} -work ${work_dir}
    
    # Set compilation options
    compile_mode mixed
    
    # Enable multi-threading
    set_nthreads ${emu_engines}
    
    # Add design libraries
    add_library -name yaoguang_lib -dir ${work_dir}
    
    # Compile RTL sources
    compile_rtl
    
    # Compile testbench
    compile_testbench
    
    # Create snapshot
    create_snapshot
    
    puts ""
    puts "=========================================="
    puts "Compilation Completed Successfully!"
    puts "=========================================="
}

###############################################################################
# Compile RTL Sources
###############################################################################

proc compile_rtl {} {
    global rtl_dir
    
    puts "Compiling RTL sources..."
    
    # SoC Top-level
    compile_verilog \
        -library yaoguang_lib \
        -options "-sv -g2012" \
        "${soc_top_dir}/yaoguang_soc_top.v" \
        "${soc_top_dir}/yaoguang_soc_wrapper.v"
    
    # CPU Subsystem
    compile_verilog \
        -library yaoguang_lib \
        -options "-sv -g2012" \
        "${rtl_dir}/cpu/yaoguang_cpu_top.v" \
        "${rtl_dir}/cpu/yaoguang_riscv_core.v" \
        "${rtl_dir}/cpu/yaoguang_plic.v" \
        "${rtl_dir}/cpu/yaoguang_clint.v" \
        "${rtl_dir}/cpu/yaoguang_tlb.v" \
        "${rtl_dir}/cpu/yaoguang_cache_l1.v"
    
    # NoC / Interconnect
    compile_verilog \
        -library yaoguang_lib \
        -options "-sv -g2012" \
        "${rtl_dir}/noc/yaoguang_noc.v" \
        "${rtl_dir}/noc/yaoguang_axi_crossbar.v" \
        "${rtl_dir}/noc/yaoguang_ahb_bridge.v" \
        "${rtl_dir}/noc/yaoguang_arbiter.v" \
        "${rtl_dir}/noc/yaoguang_router.v"
    
    # Memory Subsystem
    compile_verilog \
        -library yaoguang_lib \
        -options "-sv -g2012" \
        "${rtl_dir}/memory/yaoguang_ddr_ctrl.v" \
        "${rtl_dir}/memory/yaoguang_ddr_phy.v" \
        "${rtl_dir}/memory/yaoguang_sram_ctrl.v" \
        "${rtl_dir}/memory/yaoguang_cache_controller.v"
    
    # Peripherals
    compile_verilog \
        -library yaoguang_lib \
        -options "-sv -g2012" \
        "${rtl_dir}/peripherals/yaoguang_uart.v" \
        "${rtl_dir}/peripherals/yaoguang_gpio.v" \
        "${rtl_dir}/peripherals/yaoguang_spi.v" \
        "${rtl_dir}/peripherals/yaoguang_i2c.v" \
        "${rtl_dir}/peripherals/yaoguang_timer.v" \
        "${rtl_dir}/peripherals/yaoguang_pwm.v" \
        "${rtl_dir}/peripherals/yaoguang_wdog.v" \
        "${rtl_dir}/peripherals/yaoguang_rtc.v"
    
    # DMA
    compile_verilog \
        -library yaoguang_lib \
        -options "-sv -g2012" \
        "${rtl_dir}/dma/yaoguang_dma.v" \
        "${rtl_dir}/dma/yaoguang_dma_channel.v"
    
    # Safety Island
    compile_verilog \
        -library yaoguang_lib \
        -options "-sv -g2012 -safety" \
        "${rtl_dir}/safety/yaoguang_safety_island.v" \
        "${rtl_dir}/safety/yaoguang_lockstep.v" \
        "${rtl_dir}/safety/yaoguang_ecc_encoder.v" \
        "${rtl_dir}/safety/yaoguang_ecc_decoder.v" \
        "${rtl_dir}/safety/yaoguang_parity_checker.v"
    
    # Utility Blocks
    compile_verilog \
        -library yaoguang_lib \
        -options "-sv -g2012" \
        "${rtl_dir}/utils/yaoguang_clock_manager.v" \
        "${rtl_dir}/utils/yaoguang_reset_manager.v" \
        "${rtl_dir}/utils/yaoguang_reset_sync.v" \
        "${rtl_dir}/utils/yaoguang_pulser.v" \
        "${rtl_dir}/utils/yaoguang_filter.v"
    
    puts "RTL compilation completed"
}

###############################################################################
# Compile Testbench
###############################################################################

proc compile_testbench {} {
    global rtl_dir
    
    puts "Compiling testbench..."
    
    # Top-level testbench
    compile_verilog \
        -library yaoguang_lib \
        -options "-sv -g2012" \
        "${rtl_dir}/verification/yaoguang_soc_tb.v"
    
    # Memory models
    compile_verilog \
        -library yaoguang_lib \
        -options "-sv" \
        "${rtl_dir}/verification/ddr/yaoguang_ddr4_model.sv" \
        "${rtl_dir}/verification/ddr/yaoguang_sram_model.sv"
    
    # Peripheral BFM
    compile_verilog \
        -library yaoguang_lib \
        -options "-sv" \
        "${rtl_dir}/verification/bfm/yaoguang_uart_bfm.sv" \
        "${rtl_dir}/verification/bfm/yaoguang_gpio_bfm.sv" \
        "${rtl_dir}/verification/bfm/yaoguang_spi_bfm.sv"
    
    # Scoreboard and Monitor
    compile_verilog \
        -library yaoguang_lib \
        -options "-sv" \
        "${rtl_dir}/verification/yaoguang_scoreboard.sv" \
        "${rtl_dir}/verification/yaoguang_coverage.sv"
    
    puts "Testbench compilation completed"
}

###############################################################################
# Create Snapshot
###############################################################################

proc create_snapshot {} {
    global soc_top_dir snapshot_dir
    
    puts "Creating emulation snapshot..."
    
    # Define snapshot top
    set snapshot_top "yaoguang_soc_tb"
    
    # Create snapshot with elaboration
    elab_snapshot \
        -top ${snapshot_top} \
        -snapshot yaoguang_soc_emulation \
        -dir ${snapshot_dir} \
        -work yaoguang_lib \
        -emu_engine 8 \
        -emu_time_scale 1ns \
        -options "-access +rwc"
    
    puts "Snapshot created: ${snapshot_dir}/yaoguang_soc_emulation"
}

###############################################################################
# Configuration for Emulation
###############################################################################

proc configure_emulation {} {
    global emu_clock_period
    
    puts "Configuring emulation runtime..."
    
    # Set clock period
    set_emu_time_scale -period ${emu_clock_period} -unit ns
    
    # Enable debug features
    set_emu_debug -enable wave -enable log -enable coverage
    
    # Configure signal capture
    set_emu_signal_capture -scope all -depth 10000
    
    # Set memory initialization
    set_emu_memory_init -enable -format hex
    
    puts "Emulation configuration completed"
}

###############################################################################
# Partition Design for Scalability
###############################################################################

proc partition_design {} {
    global rtl_dir
    
    puts "Partitioning design for emulation..."
    
    # Define partitions
    partition_design -module yaoguang_cpu_top -name CPU_Partition
    partition_design -module yaoguang_noc -name NoC_Partition
    partition_design -module yaoguang_ddr_ctrl -name DDR_Partition
    partition_design -module yaoguang_safety_island -name Safety_Partition
    
    # Set partition boundaries
    set_partition_boundary -from CPU_Partition -to NoC_Partition -type clock_domain_crossing
    set_partition_boundary -from NoC_Partition -to DDR_Partition -type axi_interconnect
    set_partition_boundary -from CPU_Partition -to Safety_Partition -type lockstep
    
    # Configure inter-partition communication
    set_partition_communication -async -buffer_depth 16
    
    puts "Design partitioning completed"
}

###############################################################################
# Clock Domain Configuration
###############################################################################

proc configure_clock_domains {} {
    global emu_clock_period
    
    puts "Configuring clock domains..."
    
    # Primary clock
    create_clock -name sys_clk -period ${emu_clock_period}
    
    # Generated clocks
    create_generated_clock -name cpu_clk -source sys_clk -divide_by 1 -multiply_by 4
    create_generated_clock -name noc_clk -source sys_clk -divide_by 1 -multiply_by 2
    create_generated_clock -name ddr_clk -source sys_clk -divide_by 1 -multiply_by 2
    create_generated_clock -name peri_clk -source sys_clk -divide_by 1 -multiply_by 1
    create_generated_clock -name safety_clk -source sys_clk -divide_by 1 -multiply_by 1
    
    # Async clock groups
    set_clock_groups -asynchronous \
        -group {sys_clk} \
        -group {cpu_clk} \
        -group {noc_clk} \
        -group {ddr_clk} \
        -group {peri_clk} \
        -group {safety_clk}
    
    puts "Clock domains configured"
}

###############################################################################
# Memory Initialization
###############################################################################

proc initialize_memories {} {
    global rtl_dir
    
    puts "Initializing memories..."
    
    # Boot ROM
    init_memory \
        -file "${rtl_dir}/verification/bootrom.mem" \
        -format hex \
        -width 32 \
        -depth 0x1000 \
        -instance yaoguang_soc_tb.yaoguang_soc_top.boot_rom
    
    # Instruction RAM
    init_memory \
        -file "${rtl_dir}/verification/instr_mem.mem" \
        -format hex \
        -width 32 \
        -depth 0x10000 \
        -instance yaoguang_soc_tb.yaoguang_soc_top.instr_ram
    
    # Data RAM
    init_memory \
        -file "${rtl_dir}/verification/data_mem.mem" \
        -format hex \
        -width 32 \
        -depth 0x10000 \
        -instance yaoguang_soc_tb.yaoguang_soc_top.data_ram
    
    puts "Memories initialized"
}

###############################################################################
# Runtime Configuration
###############################################################################

proc configure_runtime {} {
    global emu_platform
    
    puts "Configuring runtime settings..."
    
    # Set platform-specific options
    switch ${emu_platform} {
        PALLADIUM_Z1 {
            set_emu_option -max_waves 64
            set_emu_option -max_memories 128
        }
        PALLADIUM_Z2 {
            set_emu_option -max_waves 256
            set_emu_option -max_memories 512
            set_emu_option -enable_xprof
        }
    }
    
    # Enable checkpoint support
    set_emu_option -checkpoint enable
    
    # Configure error handling
    set_emu_error_handling -stop_on_error -max_errors 100
    
    # Enable coverage collection
    set_emu_coverage -enable -type all
    
    puts "Runtime settings configured"
}

###############################################################################
# Generate Compilation Report
###############################################################################

proc generate_report {} {
    global snapshot_dir
    
    puts "Generating compilation report..."
    
    # Compilation summary
    report_compile_summary -file "${snapshot_dir}/compile_summary.txt"
    
    # Resource utilization
    report_resource_utilization -file "${snapshot_dir}/resource_utilization.txt"
    
    # Timing summary
    report_timing_summary -file "${snapshot_dir}/timing_summary.txt"
    
    # Partition report
    report_partitions -file "${snapshot_dir}/partition_report.txt"
    
    puts "Reports generated in ${snapshot_dir}"
}

###############################################################################
# Main Compilation Flow
###############################################################################

proc main {} {
    # Compile design
    compile_design
    
    # Configure emulation
    configure_emulation
    
    # Partition design
    partition_design
    
    # Configure clock domains
    configure_clock_domains
    
    # Initialize memories
    initialize_memories
    
    # Configure runtime
    configure_runtime
    
    # Generate reports
    generate_report
    
    puts ""
    puts "=========================================="
    puts "Palladium Compilation Complete!"
    puts "=========================================="
    puts ""
    puts "Next steps:"
    puts "  1. Review compilation report"
    puts "  2. Load snapshot: emu -load_snapshot ${snapshot_dir}/yaoguang_soc_emulation"
    puts "  3. Run simulation: emu -run"
}

# Run compilation
main

# Exit compilation mode
quit
