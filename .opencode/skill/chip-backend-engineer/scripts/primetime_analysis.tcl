#!/usr/bin/env tcl
#
# PrimeTime时序分析脚本
# 适用于Synopsys PrimeTime进行setup/hold时序分析
#
# 使用方法:
# pt_shell -f primetime_analysis.tcl -output_file primetime.log
#

# ============================================================================
# 1. 环境设置
# ============================================================================

# 清理环境
# remove_design -all

# 设置库搜索路径
# TODO: 替换为实际的库路径
# set_app_var search_path ". ./libs /path/to/libraries"

# 设置目标库
# TODO: 替换为实际的库文件
# set_app_var target_library "your_std_cell_lib.db"
# set_app_var link_library "* $target_library"

# 设置多工艺角（如果需要）
# TODO: 根据实际工艺角配置
# set_app_var target_library "tt_0p9v_25c.db ss_0p81v_125c.db ff_0p99v_-40c.db"
# set_app_var link_library "* tt_0p9v_25c.db ss_0p81v_125c.db ff_0p99v_-40c.db"

# 设置多工艺角
# set_analysis_view -setup {ss_0p81v_125c} -hold {ff_0p99v_-40c}

# ============================================================================
# 2. 读取设计
# ============================================================================

# 读取网表
# TODO: 替换为实际的网表文件
# read_verilog -netlist ./netlists/synthesized.v
# read_verilog -netlist ./netlists/${top_design}_final.v

# 设置顶层设计
# TODO: 替换为实际的顶层设计名称
# current_design your_top_design
# link

# 检查设计
# check_design > reports/design_check.rpt

# ============================================================================
# 3. 加载约束
# ============================================================================

# 读取SDC约束
# TODO: 替换为实际的SDC文件
# read_sdc ./constraints/synthesized.sdc
# read_sdc ./constraints/${top_design}_final.sdc

# 检查时序约束
# check_timing > reports/timing_check.rpt

# ============================================================================
# 4. 加载寄生参数
# ============================================================================

# 读取SPEF寄生参数文件
# TODO: 替换为实际的SPEF文件
# read_parasitics ./netlists/synthesized.spef
# read_parasitics ./netlists/${top_design}.spef

# 或读取SDF文件（如果使用SDF）
# read_sdf ./netlists/${top_design}.sdf

# 或读取DEF文件提取寄生参数
# extract_rc -corner tt_0p9v_25c

# ============================================================================
# 5. 时序更新
# ============================================================================

# 更新时序
update_timing

# 生成时序摘要
report_timing_summary > reports/timing_summary.rpt

# ============================================================================
# 6. Setup时序分析
# ============================================================================

# 创建reports目录
file mkdir reports

# Setup时序分析
# 报告最长路径
report_timing \
  -delay_type max \
  -max_paths 10 \
  -input_pins \
  -nets \
  -transition_time \
  -capacitance \
  > reports/timing_setup_top10.rpt

# Setup时序报告（详细）
report_timing \
  -delay_type max \
  -max_paths 20 \
  -path_type full \
  -significant_digits 4 \
  > reports/timing_setup_detailed.rpt

# Setup违例路径
report_timing \
  -delay_type max \
  -max_paths 50 \
  -slack_lesser_than 0.1 \
  > reports/timing_setup_violations.rpt

# 端到端时序报告
report_timing \
  -delay_type max \
  -max_paths 10 \
  -from [all_inputs] \
  -to [all_outputs] \
  > reports/timing_setup_io.rpt

# ============================================================================
# 7. Hold时序分析
# ============================================================================

# Hold时序分析
# 报告最短路径
report_timing \
  -delay_type min \
  -max_paths 10 \
  -input_pins \
  -nets \
  -transition_time \
  -capacitance \
  > reports/timing_hold_top10.rpt

# Hold时序报告（详细）
report_timing \
  -delay_type min \
  -max_paths 20 \
  -path_type full \
  -significant_digits 4 \
  > reports/timing_hold_detailed.rpt

# Hold违例路径
report_timing \
  -delay_type min \
  -max_paths 50 \
  -slack_lesser_than 0.0 \
  > reports/timing_hold_violations.rpt

# ============================================================================
# 8. 时序路径分类和分析
# ============================================================================

# 按起点分类
# all_inputs - [all_registers]
# [all_registers] - [all_registers]
# [all_registers] - [all_outputs]

# 寄存器到寄存器路径
report_timing \
  -delay_type max \
  -max_paths 10 \
  -from [all_registers -edge_triggered] \
  -to [all_registers -edge_triggered] \
  > reports/timing_setup_reg2reg.rpt

# 输入到寄存器路径
report_timing \
  -delay_type max \
  -max_paths 10 \
  -from [all_inputs] \
  -to [all_registers -edge_triggered] \
  > reports/timing_setup_in2reg.rpt

# 寄存器到输出路径
report_timing \
  -delay_type max \
  -max_paths 10 \
  -from [all_registers -edge_triggered] \
  -to [all_outputs] \
  > reports/timing_setup_reg2out.rpt

# ============================================================================
# 9. 时钟树分析
# ============================================================================

# 时钟skew报告
report_clock_timing -type skew > reports/clock_skew.rpt

# 时钟转换时间报告
report_clock_timing -type transition > reports/clock_transition.rpt

# 时钟传播报告
report_clock -propagated > reports/clock_propagation.rpt

# 时钟门控报告
report_clock_gating -verbose > reports/clock_gating.rpt

# ============================================================================
# 10. 约束报告
# ============================================================================

# 约束违例报告
report_constraint \
  -all_violators \
  > reports/constraint_violations.rpt

# 最大扇出报告
report_constraint -max_fanout > reports/max_fanout.rpt

# 最大转换时间报告
report_constraint -max_transition > reports/max_transition.rpt

# 最大电容报告
report_constraint -max_capacitance > reports/max_capacitance.rpt

# ============================================================================
# 11. 功耗分析
# ============================================================================

# 读取活动文件（SAIF）
# TODO: 替换为实际的SAIF文件
# read_saif -input ./simulation/${top_design}.saif -instance ${top_design}

# 生成功耗报告
# report_power -hierarchy > reports/power.rpt
# report_power -hier -sort_by total > reports/power_sorted.rpt

# 泄漏功耗报告
# report_power -leakage > reports/power_leakage.rpt

# 动态功耗报告
# report_power -dynamic > reports/power_dynamic.rpt

# ============================================================================
# 12. 信号完整性分析（如果需要）
# ============================================================================

# 启用SI分析
# set si_enable_analysis true
# set si_enable_propagation true

# 检查SI时序
# check_si_timing -nets [all_nets] > reports/si_timing.rpt

# ============================================================================
# 13. 时序分析和收敛策略
# ============================================================================

# 识别关键路径
# TODO: 根据项目需求调整阈值
# 报告slack < 0.5ns的路径
report_timing \
  -delay_type max \
  -slack_lesser_than 0.5 \
  -max_paths 50 \
  > reports/critical_paths.rpt

# 关键路径摘要
report_timing \
  -delay_type max \
  -max_paths 100 \
  -slack_lesser_than 0.0 \
  -significant_digits 3 \
  > reports/critical_paths_summary.rpt

# ============================================================================
# 14. QOR和覆盖率报告
# ============================================================================

# QOR报告
report_qor > reports/qor.rpt

# 时序覆盖率
report_coverage -shadow > reports/coverage.rpt

# 未约束的端点
report_unconstrained > reports/unconstrained.rpt

# ============================================================================
# 15. 导出结果
# ============================================================================

# 导出时序约束（用于后续工具）
# write_sdc -nosplit reports/${top_design}_pt.sdc

# 导出时序报告（CSV格式）
# report_timing -format single_column -max_paths 10 > reports/timing_setup_top10.csv

# 退出PrimeTime
# exit
