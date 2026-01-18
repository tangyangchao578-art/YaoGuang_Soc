#!/usr/bin/env tcl
#
# ICC2 布局布线完整流程脚本
# 适用于Synopsys ICC2进行从网表到版图的物理实现
#
# 使用方法:
# icc2_shell -f icc2_pnr.tcl -output_file icc2_pnr.log
#

# ============================================================================
# 1. 环境设置
# ============================================================================

# 清理环境
# remove_design -all

# 设置工作目录
# TODO: 替换为实际的工作目录
# set top_design your_top_design
# set work_dir "./work"
# set reports_dir "$work_dir/reports"
# set netlist_dir "$work_dir/netlists"
# set gds_dir "$work_dir/gds"

# 创建工作目录
# file mkdir $work_dir
# file mkdir $reports_dir
# file mkdir $netlist_dir
# file mkdir $gds_dir

# ============================================================================
# 2. 创建库和导入设计
# ============================================================================

# 创建ICC2库
# TODO: 替换为实际的技术文件和库路径
# create_lib ${top_design}_lib \
#   -tech tech.tf \
#   -ref_libs "ref_lib1.lef ref_lib2.lef" \
#   -lef "${top_design}.lef"

# 导入设计
# TODO: 替换为实际的网表文件
# import_designs \
#   ./netlists/synthesized.v \
#   -format verilog \
#   -top $top_design

# 保存库
# save_lib ${top_design}_lib

# ============================================================================
# 3. 加载约束
# ============================================================================

# 加载SDC约束
# TODO: 替换为实际的SDC文件
# read_sdc ./constraints/synthesized.sdc

# 加载UPF功耗意图（如果需要）
# TODO: 替换为实际的UPF文件
# read_upf ./constraints/your_design.upf

# ============================================================================
# 4. Floorplan设计
# ============================================================================

# 创建floorplan
# TODO: 根据实际设计调整参数
# create_floorplan \
#   -core_margins_by die \
#   -die_size {0 0 500 500} \
#   -left_io2core 20 \
#   -right_io2core 20 \
#   -bottom_io2core 20 \
#   -top_io2core 20

# 或使用利用率创建floorplan
# create_floorplan \
#   -core_utilization 0.7 \
#   -left_io2core 20 \
#   -right_io2core 20 \
#   -bottom_io2core 20 \
#   -top_io2core 20

# 保存floorplan
# save_lib ${top_design}_lib

# ============================================================================
# 5. 电源网络设计
# ============================================================================

# 创建电源网络
# create_net -power VDD
# create_net -ground VSS

# 创建M1和M2的电源环
# create_power_straps \
#   -nets {VDD VSS} \
#   -layer M1 \
#   -width 2 \
#   -pitch 20 \
#   -start {50 50} \
#   -num_straps 10 \
#   -direction horizontal

# create_power_straps \
#   -nets {VDD VSS} \
#   -layer M2 \
#   -width 2 \
#   -pitch 20 \
#   -start {50 50} \
#   -num_straps 10 \
#   -direction vertical

# 创建高层电源条（M5/M6）
# create_power_straps \
#   -nets {VDD VSS} \
#   -layer M5 \
#   -width 5 \
#   -pitch 100 \
#   -direction vertical

# 连接电源网络到IO pads
# TODO: 根据实际IO pads调整
# connect_pg_pins -automatic

# 连接宏单元的电源
# connect_pg_pins -macro_pin

# 保存电源网络
# save_lib ${top_design}_lib

# ============================================================================
# 6. 放置宏单元
# ============================================================================

# 放置宏单元（如果有）
# TODO: 根据实际宏单元名称和位置调整
# place_macro \
#   -macros {mem1 mem2} \
#   -locations {{100 100} {300 100}} \
#   -orientations {R0 R0}

# 保存宏单元放置
# save_lib ${top_design}_lib

# ============================================================================
# 7. 标准单元放置
# ============================================================================

# 初始化放置
# initialize_floorplan \
#   -core_utilization 0.7 \
#   -no_auto_create_boundaries

# 运行放置
# place_design

# 放置后优化
# place_opt_design -congestion

# 生成放置报告
# report_congestion > $reports_dir/congestion.rpt
# report_utilization > $reports_dir/utilization.rpt
# report_qor > $reports_dir/qor_post_place.rpt

# 保存放置结果
# save_lib ${top_design}_lib

# ============================================================================
# 8. 时钟树综合（CTS）
# ============================================================================

# 创建时钟树规范
# create_clock_tree_spec -output cts.spec

# TODO: 如果需要自定义CTS参数，编辑cts.spec文件

# 执行CTS
# clock_design -spec cts.spec

# CTS后优化
# clock_opt_design

# 生成CTS报告
# report_clock_tree > $reports_dir/clock_tree.rpt
# report_clock_timing -type skew > $reports_dir/clock_skew.rpt
# report_clock_timing -type transition > $reports_dir/clock_transition.rpt

# 保存CTS结果
# save_lib ${top_design}_lib

# ============================================================================
# 9. 路由（Routing）
# ============================================================================

# 特殊路由（电源、时钟）
# route_special -connect {corePin} \
#   -layer_change_range {M1 M5} \
#   -block_pin_target nearest_target \
#   -core_pin_target first_after_row_end \
#   -allow_jogged 1 \
#   -crossover_via_layer_range {M1 M5}

# 全局路由
# route_global

# 详细路由
# route_design

# 路由后优化
# route_opt_design

# 路由后信号完整性优化
# route_opt_design -si_aware

# 生成路由报告
# report_route -wire > $reports_dir/route_wire.rpt
# report_route -via > $reports_dir/route_via.rpt
# report_congestion > $reports_dir/congestion_post_route.rpt

# 保存路由结果
# save_lib ${top_design}_lib

# ============================================================================
# 10. 最终时序优化
# ============================================================================

# 时序优化（Setup）
# time_design -post_route -hold -setup

# 时序优化（Hold）
# time_design -post_route -hold

# 生成时序报告
# report_timing -max_paths 10 > $reports_dir/timing_setup_final.rpt
# report_timing -delay_type min -max_paths 10 > $reports_dir/timing_hold_final.rpt

# 保存最终结果
# save_lib ${top_design}_lib

# ============================================================================
# 11. 寄生参数提取
# ============================================================================

# 提取寄生参数
# TODO: 根据实际工艺角调整
# extract_parasitics -rc_corner tt_0p9v_25c

# 更新时序
# update_timing

# 生成寄生参数报告
# report_parasitics > $reports_dir/parasitics.rpt

# 导出SPEF文件
# write_parasitics \
#   -spef_file ${netlist_dir}/${top_design}.spef \
#   -rc_corner tt_0p9v_25c

# 保存寄生参数提取结果
# save_lib ${top_design}_lib

# ============================================================================
# 12. 最终检查和导出
# ============================================================================

# 最终QOR报告
# report_qor > $reports_dir/qor_final.rpt

# 最终面积报告
# report_area -hierarchy > $reports_dir/area_final.rpt

# 最终DRC检查
# verify_drc > $reports_dir/drc_final.rpt

# 导出DEF文件
# write_def \
#   -output ${netlist_dir}/${top_design}.def \
#   -version 5.8

# 导出GDS文件
# TODO: 替换为实际的map文件
# stream_out ${gds_dir}/${top_design}.gds \
#   -map_file gds_map.txt \
#   -structure_name $top_design

# 导出网表
# write_verilog \
#   -hierarchy \
#   -output ${netlist_dir}/${top_design}_final.v

# 导出SDC约束
# write_sdc \
#   -nosplit \
#   -output ${constraints_dir}/${top_design}_final.sdc

# 导出SDC用于静态时序分析
# write_sdc -nosplit ${netlist_dir}/${top_design}_sta.sdc

# ============================================================================
# 13. 完成流程
# ============================================================================

# 保存最终库
# save_lib ${top_design}_lib

# 退出ICC2
# exit
