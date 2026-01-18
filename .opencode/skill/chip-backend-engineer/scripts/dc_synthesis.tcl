#!/usr/bin/env tcl
#
# Design Compiler综合脚本模板
# 适用于Synopsys DC进行RTL到网表的综合
#
# 使用方法:
# dc_shell -f dc_synthesis.tcl -output_file dc_synthesis.log
#

# ============================================================================
# 1. 环境设置
# ============================================================================

# 设置工作目录
set_app_var target_library "your_std_cell_lib.db"
set_app_var link_library "* $target_library"
set_app_var search_path ". ./libs /path/to/libraries"

# 设置库文件
# TODO: 替换为实际的库文件路径
# set_app_var target_library "tt_0p9v_25c.db"
# set_app_var link_library "* tt_0p9v_25c.db ss_0p81v_125c.db"

# ============================================================================
# 2. 读取设计
# ============================================================================

# 读取RTL代码
# TODO: 替换为实际的RTL文件
# read_verilog -autoread -top your_top_module ./rtl

# 或指定特定文件
# read_verilog your_design.v

# 设置顶层设计
# current_design your_top_module
# link

# 检查设计
# check_design > reports/design_check_pre_compile.rpt

# ============================================================================
# 3. 约束设置
# ============================================================================

# 时钟定义
# TODO: 根据实际设计修改时钟约束
# create_clock -name clk -period 10 [get_ports clk]

# 时钟不确定性
# set_clock_uncertainty -setup 0.5 [get_clocks clk]
# set_clock_uncertainty -hold 0.1 [get_clocks clk]

# 时钟转换时间
# set_clock_transition -rise 0.2 [get_clocks clk]
# set_clock_transition -fall 0.2 [get_clocks clk]

# 输入延迟约束
# TODO: 根据实际设计修改输入延迟
# set_input_delay -clock clk -max 2.0 [get_ports data_in*]
# set_input_delay -clock clk -min 0.5 [get_ports data_in*]

# 输出延迟约束
# TODO: 根据实际设计修改输出延迟
# set_output_delay -clock clk -max 3.0 [get_ports data_out*]
# set_output_delay -clock clk -min 1.0 [get_ports data_out*]

# 输入驱动
# TODO: 根据实际设计修改驱动单元
# set_driving_cell -lib_cell INVX1 [get_ports data_in*]

# 输出负载
# TODO: 根据实际设计修改输出负载
# set_load 0.5 [get_ports data_out*]

# 多周期路径约束
# TODO: 根据实际设计添加多周期路径
# set_multicycle_path -setup 2 -from [get_cells slow_path*]
# set_multicycle_path -hold 1 -from [get_cells slow_path*]

# 虚假路径约束
# TODO: 根据实际设计添加虚假路径
# set_false_path -from [get_ports reset_n]

# ============================================================================
# 4. 综合优化
# ============================================================================

# 检查时序约束
# check_timing > reports/timing_check.rpt

# 运行综合
# TODO: 根据优化目标选择综合策略
# compile_ultra              # 默认优化（平衡）
# compile_ultra -area_high_effort_script      # 面积优化
# compile_ultra -timing_high_effort_script    # 时序优化
# compile_ultra -power_high_effort_script     # 功耗优化

# 优化设置
# set_compile_ultra_ungroup no     # 不解组
# set_host_options -max_cores 8     # 使用8核并行

# ============================================================================
# 5. 门控时钟插入（可选）
# ============================================================================

# TODO: 如果需要门控时钟，取消以下注释
# # 检查门控时钟候选
# identify_clock_gating_elements

# # 插入门控时钟
# insert_clock_gating

# # 重新优化
# compile_ultra

# ============================================================================
# 6. 综合后分析和报告
# ============================================================================

# 创建报告目录
file mkdir reports

# 面积报告
report_area -hierarchy > reports/area.rpt
report_area -hierarchy -nosplit > reports/area_nosplit.rpt

# 时序报告
report_timing -max_paths 10 > reports/timing_setup.rpt
report_timing -delay_type min -max_paths 10 > reports/timing_hold.rpt

# 约束报告
report_constraint -all_violators > reports/constraint_violations.rpt

# 功耗报告
# TODO: 需要读取活动文件后才能生成功耗报告
# report_power -hierarchy > reports/power.rpt

# 设计规则检查
check_design > reports/design_check.rpt

# QOR报告
report_qor > reports/qor.rpt

# 单元使用报告
report_resources > reports/resources.rpt

# 时钟 gating 报告
# report_clock_gating -verbose > reports/clock_gating.rpt

# ============================================================================
# 7. 保存综合结果
# ============================================================================

# 保存网表
write -format verilog -hierarchy -output netlists/synthesized.v

# 保存约束文件
write_sdc -nosplit constraints/synthesized.sdc

# 保存DDC文件（二进制格式，加载速度快）
write -format ddc -hierarchy -output netlists/synthesized.ddc

# 保存综合报告数据库
write_parasitics -format spef -output netlists/synthesized.spef

# ============================================================================
# 8. 退出
# ============================================================================

# 退出DC shell
# exit
