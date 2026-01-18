#!/usr/bin/env tclsh
#===============================================================================
# YaoGuang SoC Synthesis Setup Script
# Version: V1.0
# Date: 2026-01-18
#===============================================================================

#===============================================================================
# 1. 工艺库路径设置
#===============================================================================
set SYNTH_HOME $env(SYNTH_HOME)

# 工艺库目录 (TSMC 5nm)
set TECH_LIB_PATH "${SYNTH_HOME}/lib/TSMC_5nm"

# 目标库文件
set TARGET_LIB_FILE "${TECH_LIB_PATH}/saed5nm_typ.db"

# 综合库文件列表
set LIB_FILES [list \
    "${TECH_LIB_PATH}/saed5nm_typ.db" \
    "${TECH_LIB_PATH}/saed5nm_min.db" \
    "${TECH_LIB_PATH}/saed5nm_max.db" \
]

#===============================================================================
# 2. 搜索路径设置
#===============================================================================
set_search_path [list \
    . \
    ${SYNTH_HOME}/../04_Design_RTL/soc_top \
    ${SYNTH_HOME}/../04_Design_RTL/ip_rtl \
    ${TECH_LIB_PATH} \
]

#===============================================================================
# 3. 库变量设置
#===============================================================================
set_app_var target_library $TARGET_LIB_FILE
set_app_var link_library "* $TARGET_LIB_FILE"

# 设置符号库
set_app_var symbol_library [list \
    "${TECH_LIB_PATH}/saed5nm.sdb" \
]

#===============================================================================
# 4. 综合选项设置
#===============================================================================

# 1) 基础设置
set_app_var verilogout_no_tri true
set_app_var hdlout_internal_busses true
set_app_var bus_inference_style "%s\[%d:%d\]"
set_app_var bus_naming_style "%s\[%d\]"

# 2) 时序分析设置
set_app_var timing_enable_multiple_clocks_per_reg true
set_app_var report_timing_longer_paths_max_paths 50

# 3) 面积单位设置
set_app_var area_unit 1
set_app_var capacitance_unit 1
set_app_var resistance_unit 1
set_app_var leakage_power_unit 1
set_app_var dynamic_power_unit 1

# 4) 编译选项
set_app_var compile_enable_prelayout_opt true
set_app_var compile_assume_inferred_clock_for_rtl false
set_app_var auto_wire_load_selection true

#===============================================================================
# 5. 时钟门控设置
#===============================================================================
set_clock_gating_style -sequential_cell latch -positive_edge_logic "integrated" -negative_edge_logic "integrated"

#===============================================================================
# 6. 常用变量导出
#===============================================================================
set DESIGN_NAME "yaoguang_soc"
set DESIGN_TOP  "soc_top"

set RTL_DIR     "${SYNTH_HOME}/../04_Design_RTL"
set OUTPUT_DIR  "${SYNTH_HOME}/../output"
set REPORT_DIR  "${SYNTH_HOME}/../reports"
set SDC_FILE    "${SYNTH_HOME}/../sdc/yaoguang_soc.sdc"

puts "\[SETUP\] Synthesis environment initialized successfully"
puts "\[SETUP\] Target Library: $TARGET_LIB_FILE"
