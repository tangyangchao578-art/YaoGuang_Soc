#!/bin/bash
###############################################################################
# YaoGuang SoC Vivado Project Creator for Versal ACAP
# Level: CV Verification Architect
# Date: 2026-01-18
###############################################################################

# This script should be sourced from Vivado TCL console
# or run with: vivado -mode tcl -source create_project.tcl

###############################################################################
# Project Configuration
###############################################################################
set project_name "YaoGuang_SoC_FPGA"
set project_dir "[expr {[file dirname [info script]]}]/../../../../06_Verification_CV/fpga/versal_acap"
set rtl_dir "[expr {[file dirname [info script]]}]/../../../../04_Design_RTL"
set xdc_dir "[expr {[file dirname [info script]]}]/../constraints"
set build_dir "./build"
set device "xcvp1902-vsva2785-1MP-e-S"
set package "neg"
set speed "-1"
set synthesis_strategy "Performance_Optimized"
set implementation_strategy "Performance_Optimized"

###############################################################################
# Create Project
###############################################################################
proc create_yaoguang_project {} {
    variable project_name
    variable project_dir
    variable build_dir
    variable device
    variable package
    variable speed
    
    puts "=========================================="
    puts "YaoGuang SoC Vivado Project Creator"
    puts "=========================================="
    puts ""
    puts "Project Name: $project_name"
    puts "Project Dir:  $project_dir"
    puts "Device:       $device$package$speed"
    puts ""
    
    # Create project directory
    if {![file exists $project_dir]} {
        file mkdir $project_dir
        puts "Created project directory: $project_dir"
    }
    
    # Create build directory
    if {![file exists "$project_dir/$build_dir"]} {
        file mkdir "$project_dir/$build_dir"
    }
    
    # Close current project if any
    if {[current_project -quiet] ne ""} {
        close_project
    }
    
    # Create new project
    create_project \
        -name $project_name \
        -dir $project_dir \
        -part ${device}${package}${speed} \
        -force \
        -quiet
    
    # Set project settings
    set_project_settings
    
    # Add sources
    add_sources
    
    # Add constraints
    add_constraints
    
    # Configure bitstream settings
    configure_bitstream
    
    puts ""
    puts "=========================================="
    puts "Project Created Successfully!"
    puts "=========================================="
}

###############################################################################
# Set Project Settings
###############################################################################
proc set_project_settings {} {
    variable synthesis_strategy
    variable implementation_strategy
    
    puts "Configuring project settings..."
    
    # Set synthesis strategy
    set_param synth.checkpointMode 2
    set_param rtl.skipIdentifiedConstants.tclInferred 1
    
    # Set implementation strategy
    set_param project.vivadoISFlow 1
    
    # Enable incremental synthesis
    set_param synth.incremental 1
    
    # Set default library
    set_default_lib -name work
    
    puts "Project settings configured"
}

###############################################################################
# Add RTL Sources
###############################################################################
proc add_sources {} {
    variable rtl_dir
    
    puts "Adding RTL sources..."
    
    # Add SoC top-level RTL
    add_files -norecurse \
        "$rtl_dir/soc_top/yaoguang_soc_top.v" \
        "$rtl_dir/soc_top/yaoguang_soc_wrapper.v"
    
    # Add CPU subsystem
    add_files -norecurse \
        "$rtl_dir/ip_rtl/cpu/yaoguang_cpu_top.v" \
        "$rtl_dir/ip_rtl/cpu/yaoguang_plic.v" \
        "$rtl_dir/ip_rtl/cpu/yaoguang_clint.v"
    
    # Add NoC/Interconnect
    add_files -norecurse \
        "$rtl_dir/ip_rtl/noc/yaoguang_noc.v" \
        "$rtl_dir/ip_rtl/noc/yaoguang_axi_crossbar.v" \
        "$rtl_dir/ip_rtl/noc/yaoguang_ahb_bridge.v"
    
    # Add Memory controller
    add_files -norecurse \
        "$rtl_dir/ip_rtl/memory/yaoguang_ddr_ctrl.v" \
        "$rtl_dir/ip_rtl/memory/yaoguang_sram_ctrl.v"
    
    # Add Peripherals
    add_files -norecurse \
        "$rtl_dir/ip_rtl/peripherals/yaoguang_uart.v" \
        "$rtl_dir/ip_rtl/peripherals/yaoguang_gpio.v" \
        "$rtl_dir/ip_rtl/peripherals/yaoguang_spi.v" \
        "$rtl_dir/ip_rtl/peripherals/yaoguang_i2c.v" \
        "$rtl_dir/ip_rtl/peripherals/yaoguang_timer.v" \
        "$rtl_dir/ip_rtl/peripherals/yaoguang_pwm.v" \
        "$rtl_dir/ip_rtl/peripherals/yaoguang_wdog.v"
    
    # Add DMA
    add_files -norecurse \
        "$rtl_dir/ip_rtl/dma/yaoguang_dma.v"
    
    # Add Safety Island
    add_files -norecurse \
        "$rtl_dir/ip_rtl/safety/yaoguang_safety_island.v" \
        "$rtl_dir/ip_rtl/safety/yaoguang_lockstep.v"
    
    # Add Utility
    add_files -norecurse \
        "$rtl_dir/ip_rtl/utils/yaoguang_clock_manager.v" \
        "$rtl_dir/ip_rtl/utils/yaoguang_reset_manager.v" \
        "$rtl_dir/ip_rtl/utils/yaoguang_reset_sync.v"
    
    # Add FPGA-specific files
    add_files -norecurse \
        [glob "$rtl_dir/ip_rtl/fpga/*.v"]
    
    puts "RTL sources added successfully"
}

###############################################################################
# Add Constraints
###############################################################################
proc add_constraints {} {
    variable project_dir
    variable xdc_dir
    
    puts "Adding constraint files..."
    
    # Add timing constraints
    if {[file exists "$xdc_dir/timing.xdc"]} {
        add_files -fileset constrs_1 -norecurse "$xdc_dir/timing.xdc"
        puts "Added: $xdc_dir/timing.xdc"
    } else {
        puts "WARNING: $xdc_dir/timing.xdc not found"
    }
    
    # Add pin constraints
    if {[file exists "$xdc_dir/pinout.xdc"]} {
        add_files -fileset constrs_1 -norecurse "$xdc_dir/pinout.xdc"
        puts "Added: $xdc_dir/pinout.xdc"
    }
    
    # Add physical constraints
    if {[file exists "$xdc_dir/physical.xdc"]} {
        add_files -fileset constrs_1 -norecurse "$xdc_dir/physical.xdc"
        puts "Added: $xdc_dir/physical.xdc"
    }
    
    puts "Constraint files added"
}

###############################################################################
# Configure Bitstream
###############################################################################
proc configure_bitstream {} {
    puts "Configuring bitstream settings..."
    
    # Enable bitstream compression
    set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
    
    # Set configuration mode
    set_property CONFIG_MODE JTAG [current_design]
    
    # Enable CRC check
    set_property BITSTREAM.ENABLE_CRC_CHECK TRUE [current_design]
    
    # Set power reduction mode
    set_property BITSTREAM.POWER_REDUCTION balanced [current_design]
    
    puts "Bitstream settings configured"
}

###############################################################################
# Run Synthesis
###############################################################################
proc run_synthesis {} {
    variable synthesis_strategy
    
    puts "Running synthesis..."
    puts "Strategy: $synthesis_strategy"
    
    launch_runs -to_step synth_design -strategy $synthesis_strategy
    wait_on_run [get_runs synth_1]
    
    if {[get_property STATUS [get_runs synth_1]] ne "synth_design_complete"} {
        puts "ERROR: Synthesis failed!"
        return 1
    }
    
    puts "Synthesis completed successfully"
    return 0
}

###############################################################################
# Run Implementation
###############################################################################
proc run_implementation {} {
    variable implementation_strategy
    
    puts "Running implementation..."
    puts "Strategy: $implementation_strategy"
    
    launch_runs -strategy $implementation_strategy
    wait_on_run [get_runs impl_1]
    
    if {[get_property STATUS [get_runs impl_1]] ne "impl_complete"} {
        puts "ERROR: Implementation failed!"
        return 1
    }
    
    puts "Implementation completed successfully"
    return 0
}

###############################################################################
# Generate Bitstream
###############################################################################
proc generate_bitstream {} {
    puts "Generating bitstream..."
    
    launch_runs impl_1 -to_step write_bitstream
    wait_on_run [get_runs impl_1]
    
    if {[get_property STATUS [get_runs impl_1]] ne "write_bitstream_complete"} {
        puts "ERROR: Bitstream generation failed!"
        return 1
    }
    
    puts "Bitstream generated successfully"
    return 0
}

###############################################################################
# Export Hardware
###############################################################################
proc export_hardware {} {
    variable project_dir
    
    puts "Exporting hardware to XSA..."
    
    export_hw_platform \
        -force \
        -file "$project_dir/yaoguang_soc_wrapper.xsa" \
        -format xsa
    
    puts "Hardware exported to: $project_dir/yaoguang_soc_wrapper.xsa"
}

###############################################################################
# Main Execution
###############################################################################
proc main {} {
    create_yaoguang_project
    
    # Uncomment to run full flow
    # run_synthesis
    # run_implementation
    # generate_bitstream
    # export_hardware
    
    puts ""
    puts "Project is ready for synthesis. Run the following commands:"
    puts "  launch_runs impl_1 -to_step write_bitstream"
    puts "  wait_on_run [get_runs impl_1]"
}

# Run main if script is executed
if {[info exists argv0] && $argv0 eq [info script]} {
    main
}
