#!/usr/bin/env tclsh
# YaoGuang SoC Power Analysis Script

# 设置功耗分析模式
set_power_analysis_mode -static -leakage true

# 读取设计
read_verilog yaoguang_soc_pnr.v
current_design yaoguang_soc_top
link

# 读取UPF
read_upf yaoguang_soc.upf

# 读取切换活动
read_saif -input yaoguang_soc.saif

# 设置工作条件
set_operating_conditions -library saed5nm_tt \
  -temperature 25 -voltage_scale 1.0

# 功耗分析
report_power -hierarchy -detail

# 按模块分类报告
report_power -hierarchy -sort_by total

# 功耗分布报告
foreach domain {PD_CPU PD_NPU PD_GPU PD_MEM PD_SYS PD_IO} {
  report_power -power_domain $domain
}

# 静态功耗报告
report_power -analysis_type static

# 动态功耗报告
report_power -analysis_type dynamic
