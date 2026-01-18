#!/usr/bin/env tclsh
#===============================================================================
# YaoGuang SoC Logic Synthesis Main Script
# Version: V1.0
# Date: 2026-01-18
#===============================================================================

# 源环境设置
source ./setup_dc.tcl

#===============================================================================
# 1. 打印设计信息
#===============================================================================
puts "========================================"
puts "  YaoGuang SoC Logic Synthesis"
puts "========================================"
puts "Design: $DESIGN_NAME"
puts "Top:    $DESIGN_TOP"
puts "Target Frequency: 2.0 GHz (Core/NPU), 500 MHz (System)"
puts ""

#===============================================================================
# 2. 检查文件存在
#===============================================================================
set error_flag 0

if { ![file exists $SDC_FILE] } {
    puts "\[ERROR\] SDC file not found: $SDC_FILE"
    set error_flag 1
}

if { $error_flag } {
    puts "\[ERROR\] Synthesis aborted due to missing files"
    exit 1
}

puts "\[INFO\] All required files found"
puts ""

#===============================================================================
# 3. 读取RTL文件
#===============================================================================
puts "========================================"
puts "  Step 1: Reading RTL Files"
puts "========================================"

# 读取顶层文件
read_verilog ${RTL_DIR}/soc_top/yaoguang_soc_top.v

# 读取子系统RTL文件
read_verilog ${RTL_DIR}/soc_top/cpu_subsystem.v
read_verilog ${RTL_DIR}/soc_top/npu_subsystem.v
read_verilog ${RTL_DIR}/soc_top/gpu_subsystem.v
read_verilog ${RTL_DIR}/soc_top/isp_subsystem.v
read_verilog ${RTL_DIR}/soc_top/memory_subsystem.v
read_verilog ${RTL_DIR}/soc_top/io_subsystem.v

# 读取IP RTL文件
read_verilog ${RTL_DIR}/ip_rtl/cpu_core.v
read_verilog ${RTL_DIR}/ip_rtl/npu_cluster.v
read_verilog ${RTL_DIR}/ip_rtl/gpu_core.v
read_verilog ${RTL_DIR}/ip_rtl/isp_pipeline.v
read_verilog ${RTL_DIR}/ip_rtl/ddr_controller.v
read_verilog ${RTL_DIR}/ip_rtl/pcie_controller.v
read_verilog ${RTL_DIR}/ip_rtl/gmac_controller.v
read_verilog ${RTL_DIR}/ip_rtl/spi_controller.v
read_verilog ${RTL_DIR}/ip_rtl/i2c_controller.v
read_verilog ${RTL_DIR}/ip_rtl/uart_controller.v
read_verilog ${RTL_DIR}/ip_rtl/gpio_controller.v
read_verilog ${RTL_DIR}/ip_rtl/interrupt_controller.v
read_verilog ${RTL_DIR}/ip_rtl/timer_controller.v
read_verilog ${RTL_DIR}/ip_rtl/watchdog.v
read_verilog ${RTL_DIR}/ip_rtl/clock_manager.v
read_verilog ${RTL_DIR}/ip_rtl/reset_manager.v
read_verilog ${RTL_DIR}/ip_rtl/system_controller.v
read_verilog ${RTL_DIR}/ip_rtl/axi_crossbar.v
read_verilog ${RTL_DIR}/ip_rtl/apb_bridge.v
read_verilog ${RTL_DIR}/ip_rtl/async_fifo.v

puts ""
puts "\[INFO\] RTL files loaded successfully"

#===============================================================================
# 4. 施加约束
#===============================================================================
puts ""
puts "========================================"
puts "  Step 2: Applying Constraints"
puts "========================================"

source $SDC_FILE

puts ""
puts "\[INFO\] Constraints applied successfully"

#===============================================================================
# 5. 约束检查
#===============================================================================
puts ""
puts "========================================"
puts "  Step 3: Constraint Checking"
puts "========================================"

# 检查时序约束
set timing_errors [check_timing -summary]
puts "Timing check: $timing_errors"

# 检查设计规则
set design_errors [check_design -summary]
puts "Design check: $design_errors"

if { $timing_errors > 0 || $design_errors > 0 } {
    puts "\[WARNING\] Design has constraint violations, continuing..."
}

#===============================================================================
# 6. 链接设计
#===============================================================================
puts ""
puts "========================================"
puts "  Step 4: Linking Design"
puts "========================================"

link $DESIGN_TOP

puts "\[INFO\] Design linked successfully"

#===============================================================================
# 7. 面积优化
#===============================================================================
puts ""
puts "========================================"
puts "  Step 5: Area Optimization (Pass 1)"
puts "========================================"

compile_ultra -area_high_effort_script

puts "\[INFO\] Area optimization completed"

#===============================================================================
# 8. 时序优化
#===============================================================================
puts ""
puts "========================================"
puts "  Step 6: Timing Optimization (Pass 2)"
puts "========================================"

compile_ultra -timing_high_effort_script

puts "\[INFO\] Timing optimization completed"

#===============================================================================
# 9. 时钟门控优化
#===============================================================================
puts ""
puts "========================================"
puts "  Step 7: Clock Gating Optimization"
puts "========================================"

insert_clock_gating -check_clocks -unaware

puts "\[INFO\] Clock gating optimization completed"

#===============================================================================
# 10. 功耗优化
#===============================================================================
puts ""
puts "========================================"
puts "  Step 8: Power Optimization"
puts "========================================"

set_power_options -level 3

puts "\[INFO\] Power optimization completed"

#===============================================================================
# 11. 最终优化
#===============================================================================
puts ""
puts "========================================"
puts "  Step 9: Final Optimization"
puts "========================================"

compile_ultra -no_autoungroup

puts "\[INFO\] Final optimization completed"

#===============================================================================
# 12. 报告生成
#===============================================================================
puts ""
puts "========================================"
puts "  Step 10: Generating Reports"
puts "========================================"

# 创建报告目录
file mkdir $REPORT_DIR

# 面积报告
puts "Generating area report..."
report_area -hierarchy -comparative > ${REPORT_DIR}/area.rpt
report_area > ${REPORT_DIR}/area_summary.rpt

# 时序报告
puts "Generating timing report..."
report_timing -max_paths 50 -path_type full > ${REPORT_DIR}/timing.rpt
report_timing -max_paths 20 -nworst 1 > ${REPORT_DIR}/timing_critical.rpt
report_timing -clock_group -max_paths 10 > ${REPORT_DIR}/timing_clock_groups.rpt

# 功耗报告
puts "Generating power report..."
report_power -hierarchy > ${REPORT_DIR}/power.rpt
report_power -analysis_effort high > ${REPORT_DIR}/power_detailed.rpt

# 时钟报告
puts "Generating clock report..."
report_clock -skew > ${REPORT_DIR}/clock.rpt
report_clock_gating > ${REPORT_DIR}/clock_gating.rpt

# 时序约束报告
puts "Generating constraint report..."
report_constraints -all_violators > ${REPORT_DIR}/constraints_violators.rpt
report_path_analysis > ${REPORT_DIR}/path_analysis.rpt

# 面积统计
puts ""
puts "========================================"
puts "  Area Statistics"
puts "========================================"
report_area -summary

# 时序统计
puts ""
puts "========================================"
puts "  Timing Statistics"
puts "========================================"
report_timing -summary

# 功耗统计
puts ""
puts "========================================"
puts "  Power Statistics"
puts "========================================"
report_power -summary

#===============================================================================
# 13. 输出保存
#===============================================================================
puts ""
puts "========================================"
puts "  Step 11: Saving Outputs"
puts "========================================"

# 创建输出目录
file mkdir $OUTPUT_DIR

# 保存综合网表
puts "Saving netlist..."
write -format verilog -output ${OUTPUT_DIR}/${DESIGN_NAME}_netlist.v

# 保存时序约束
puts "Saving SDC..."
write_sdc ${OUTPUT_DIR}/${DESIGN_NAME}_sdc.out.sdc

# 保存设计数据库
puts "Saving Design Database..."
write -format ddc -output ${OUTPUT_DIR}/${DESIGN_NAME}.ddc

# 保存错误日志
redirect ${OUTPUT_DIR}/check_design.rpt { check_design }
redirect ${OUTPUT_DIR}/check_timing.rpt { check_timing }

puts ""
puts "\[INFO\] Synthesis completed successfully"
puts ""

#===============================================================================
# 14. 最终检查
#===============================================================================
puts "========================================"
puts "  Final Verification"
puts "========================================"

# 检查时序违例
report_timing -max_paths 10 -slack_lesser_than 0

# 检查设计规则
check_design

puts ""
puts "========================================"
puts "  Synthesis Summary"
puts "========================================"
puts "Netlist:      ${OUTPUT_DIR}/${DESIGN_NAME}_netlist.v"
puts "SDC:          ${OUTPUT_DIR}/${DESIGN_NAME}_sdc.out.sdc"
puts "Area Report:  ${REPORT_DIR}/area.rpt"
puts "Timing Report: ${REPORT_DIR}/timing.rpt"
puts "Power Report:  ${REPORT_DIR}/power.rpt"
puts "========================================"
