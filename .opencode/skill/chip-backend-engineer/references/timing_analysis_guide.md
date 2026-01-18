# 时序分析完整指南

## 概述

本文档提供Synopsys PrimeTime时序分析的完整指南，涵盖Setup、Hold时序分析、时序违例修复和时序收敛策略。

## 1. 时序分析基础

### 1.1 时序路径类型

**1. 寄存器到寄存器路径：**
```
RegA/Q → Comb Logic → RegB/D
最常见路径，时序容易满足
```

**2. 输入到寄存器路径：**
```
Input Port → Comb Logic → Reg/D
取决于输入延迟约束
```

**3. 寄存器到输出路径：**
```
Reg/Q → Comb Logic → Output Port
需要输出负载建模
```

**4. 输入到输出路径：**
```
Input Port → Comb Logic → Output Port
纯组合路径，通常很短
```

### 1.2 时序路径组成部分

**数据路径延迟：**
- Cell延迟（内部延迟）
- 网络延迟（互连延迟）
- 输入延迟
- 输出延迟

**时钟路径延迟：**
- 时钟源到寄存器时钟端
- 时钟skew
- 时钟抖动
- 时钟不确定性

### 1.3 时序约束

**Setup时间要求：**
```
T_data_max + T_setup ≤ T_clock - T_skew - T_uncertainty
```

**Hold时间要求：**
```
T_data_min ≥ T_hold + T_skew + T_uncertainty
```

## 2. PrimeTime使用

### 2.1 环境设置

```tcl
# 清理环境
remove_design -all

# 设置库路径
set_app_var search_path ". ./libs /path/to/libraries"

# 设置目标库
set_app_var target_library "tt_0p9v_25c.db"
set_app_var link_library "* $target_library"

# 多工艺角设置
set_app_var target_library "tt_0p9v_25c.db ss_0p81v_125c.db ff_0p99v_-40c.db"
set_app_var link_library "* tt_0p9v_25c.db ss_0p81v_125c.db ff_0p99v_-40c.db"

# 设置分析视图
set_analysis_view -setup {ss_0p81v_125c} -hold {ff_0p99v_-40c}
```

### 2.2 读取设计

```tcl
# 读取网表
read_verilog -netlist ./netlists/synthesized.v

# 设置顶层设计
current_design your_top_design
link

# 检查设计
check_design > reports/design_check.rpt
```

### 2.3 加载约束和寄生参数

```tcl
# 读取SDC约束
read_sdc ./constraints/synthesized.sdc

# 检查时序约束
check_timing > reports/timing_check.rpt

# 读取寄生参数
read_parasitics ./netlists/synthesized.spef

# 或读取SDF文件
read_sdf ./netlists/synthesized.sdf

# 更新时序
update_timing
```

## 3. Setup时序分析

### 3.1 Setup时序报告

```tcl
# 报告最长路径
report_timing \
  -delay_type max \
  -max_paths 10 \
  -input_pins \
  -nets \
  -transition_time \
  -capacitance \
  > reports/timing_setup_top10.rpt

# Setup时序详细报告
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
```

### 3.2 Setup时序分析技巧

**识别关键路径：**
```tcl
# 报告所有setup违例路径
report_timing \
  -delay_type max \
  -max_paths 100 \
  -slack_lesser_than 0.0 \
  > reports/all_setup_violations.rpt

# 按起点分类
report_timing \
  -delay_type max \
  -max_paths 20 \
  -from [all_inputs] \
  -to [all_registers -edge_triggered] \
  > reports/setup_in2reg.rpt

report_timing \
  -delay_type max \
  -max_paths 20 \
  -from [all_registers -edge_triggered] \
  -to [all_registers -edge_triggered] \
  > reports/setup_reg2reg.rpt

report_timing \
  -delay_type max \
  -max_paths 20 \
  -from [all_registers -edge_triggered] \
  -to [all_outputs] \
  > reports/setup_reg2out.rpt
```

**分析关键路径：**
```tcl
# 查看特定路径
report_timing \
  -delay_type max \
  -from [get_pins regA/Q] \
  -to [get_pins regB/D] \
  > reports/path_A_to_B.rpt

# 查看路径中的瓶颈
report_path \
  -from [get_pins regA/Q] \
  -to [get_pins regB/D] \
  > reports/path_bottleneck.rpt
```

## 4. Hold时序分析

### 4.1 Hold时序报告

```tcl
# 报告最短路径
report_timing \
  -delay_type min \
  -max_paths 10 \
  -input_pins \
  -nets \
  -transition_time \
  -capacitance \
  > reports/timing_hold_top10.rpt

# Hold时序详细报告
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
```

### 4.2 Hold时序分析技巧

**识别Hold违例：**
```tcl
# 报告所有hold违例路径
report_timing \
  -delay_type min \
  -max_paths 100 \
  -slack_lesser_than 0.0 \
  > reports/all_hold_violations.rpt

# 按起点分类
report_timing \
  -delay_type min \
  -max_paths 20 \
  -from [all_inputs] \
  -to [all_registers -edge_triggered] \
  > reports/hold_in2reg.rpt

report_timing \
  -delay_type min \
  -max_paths 20 \
  -from [all_registers -edge_triggered] \
  -to [all_registers -edge_triggered] \
  > reports/hold_reg2reg.rpt
```

## 5. 时序收敛策略

### 5.1 Setup违例修复

**优先级1：关键路径优化（>100ps违例）**
```tcl
# 1. 增加驱动强度
resize_cell [get_cells inst_name] [get_lib_cells BUFFX4]

# 2. 插入缓冲器
insert_buffer [get_pins inst_name/Z] BUFFX2

# 3. 使用高速单元
set_lib_cell_purpose -include none [get_lib_cells */*]
set_lib_cell_purpose -include power [get_lib_cells */HVT*]
set_lib_cell_purpose -include power [get_lib_cells */LVT*]
```

**优先级2：中等违例修复（10-100ps）**
```tcl
# 1. 逻辑重组
set_app_var restructure_design true
set_app_var restructure_timing true

# 2. 路径平衡
balance_timing -from [get_pins start_pin] -to [get_pins end_pin]

# 3. 优化单元映射
optimize_design -timing
```

**优先级3：小违例修复（<10ps）**
```tcl
# 1. 调整约束
set_clock_latency -max 0.5 [get_clocks clk]

# 2. 优化布线
# 返回ICC2重新布线优化
```

### 5.2 Hold违例修复

**修复方法：**
```tcl
# 1. 插入延迟单元
insert_buffer [get_pins inst_name/Z] DELAY_CELL

# 2. 减小驱动强度
resize_cell [get_cells inst_name] [get_lib_cells BUFFX1]

# 3. 调整时钟树
set_clock_latency -min 0.2 [get_clocks clk]

# 4. 增加路径延迟
set_max_delay 0.5 -from [get_pins start_pin] -to [get_pins end_pin]
```

### 5.3 时序优化迭代流程

```
1. 分析时序违例
   ↓
2. 识别瓶颈（高延迟单元、高扇出、长互连）
   ↓
3. 选择优化方法（驱动、缓冲、逻辑重构）
   ↓
4. 实施优化（修改网表或约束）
   ↓
5. 重新综合/布线
   ↓
6. 重新分析时序
   ↓
7. 检查优化效果
   ↓
8. 返回步骤2，直到时序满足
```

## 6. 高级时序分析

### 6.1 时钟树分析

```tcl
# 时钟skew报告
report_clock_timing -type skew > reports/clock_skew.rpt

# 时钟转换时间报告
report_clock_timing -type transition > reports/clock_transition.rpt

# 时钟传播报告
report_clock -propagated > reports/clock_propagation.rpt

# 时钟门控报告
report_clock_gating -verbose > reports/clock_gating.rpt

# 时钟延迟报告
report_clock -attributes > reports/clock_attributes.rpt
```

### 6.2 信号完整性分析

```tcl
# 启用SI分析
set si_enable_analysis true
set si_enable_propagation true

# 检查SI时序
check_si_timing -nets [all_nets] > reports/si_timing.rpt

# SI毛刺分析
check_si_glitch -nets [all_nets] > reports/si_glitch.rpt

# 串扰分析
report_si_timing -max_paths 10 > reports/si_crosstalk.rpt
```

### 6.3 OCV分析

```tcl
# 设置OCV因子
set_timing_derate -early 0.95 -late 1.05

# 报告OCV分析结果
report_timing -max_paths 10 -derate > reports/ocv_timing.rpt

# 按OCV报告
report_analysis_coverage -type ocv > reports/ocv_coverage.rpt
```

### 6.4 多模式多角分析

```tcl
# 定义多个corner
set corner_ss [create_corner ss_corner]
set_corner_info -name ss_corner -timing Prepare {ss_0p81v_125c.db}

set corner_ff [create_corner ff_corner]
set_corner_info -name ff_corner -timing Prepare {ff_0p99v_-40c.db}

# 定义多个模式
set mode_func [create_mode func_mode]
set_mode_info -name func_mode -sdc_file func.sdc

set mode_test [create_mode test_mode]
set_mode_info -name test_mode -sdc_file test.sdc

# 定义分析视图
set_analysis_view \
  -setup {{func_mode ss_corner} {test_mode ss_corner}} \
  -hold {{func_mode ff_corner} {test_mode ff_corner}}

# 运行分析
update_timing

# 报告特定视图的时序
report_timing -view {func_mode ss_corner} -max_paths 10
```

## 7. 时序调试技巧

### 7.1 定位问题

**使用report_timing的选项：**
```tcl
# 显示电容
report_timing -max_paths 10 -capacitance > reports/timing_with_cap.rpt

# 显示转换时间
report_timing -max_paths 10 -transition_time > reports/timing_with_transition.rpt

# 显示网络
report_timing -max_paths 10 -nets > reports/timing_with_nets.rpt

# 显示输入引脚
report_timing -max_paths 10 -input_pins > reports/timing_with_pins.rpt

# 完整路径信息
report_timing -max_paths 10 -path_type full \
  -signifcant_digits 4 > reports/timing_full_path.rpt
```

### 7.2 路径分解分析

```tcl
# 报告路径中的单元延迟
report_cell -latency [get_cells -filter "@full_name =~ inst_name*"]

# 报告网络延迟
report_net -latency [get_nets -filter "@full_name =~ net_name*"]

# 报告路径统计
report_path -from [get_pins start] -to [get_pins end]
```

### 7.3 生成时序报告

```tcl
# Setup时序摘要
report_timing -delay_type max -max_paths 10 -summary \
  > reports/timing_setup_summary.rpt

# Hold时序摘要
report_timing -delay_type min -max_paths 10 -summary \
  > reports/timing_hold_summary.rpt

# 时序违例摘要
report_timing_summary > reports/timing_summary.rpt

# QOR摘要
report_qor > reports/qor.rpt

# 未约束的端点
report_unconstrained > reports/unconstrained.rpt
```

## 8. 时序分析检查清单

### 8.1 分析前检查
- [ ] 网表正确加载
- [ ] 库文件正确设置
- [ ] SDC约束完整加载
- [ ] 寄生参数正确加载
- [ ] 设计成功link
- [ ] 时钟定义正确

### 8.2 分析中检查
- [ ] Setup时序满足要求
- [ ] Hold时序满足要求
- [ ] 无关键时序违例
- [ ] 时钟skew在合理范围
- [ ] 无未约束的路径
- [ ] 功耗分析结果合理

### 8.3 分析后检查
- [ ] 时序报告完整
- [ ] QOR报告生成
- [ ] 覆盖率报告生成
- [ ] 违例分析完成
- [ ] 优化建议明确

## 9. 常见问题和解决方案

### 9.1 Setup违例

**问题：** Setup时间不满足
- 检查时钟周期约束
- 分析关键路径延迟
- 优化路径逻辑
- 增加驱动强度
- 插入流水线

### 9.2 Hold违例

**问题：** Hold时间不满足
- 检查时钟skew
- 插入延迟单元
- 减小驱动强度
- 调整时钟树

### 9.3 时钟skew过大

**问题：** 时钟skew超过预算
- 重新平衡时钟树
- 检查时钟网络负载
- 优化时钟缓冲器分布

### 9.4 未约束路径

**问题：** 存在未约束的时序路径
- 检查SDC约束完整性
- 添加必要的约束
- 设置合理的虚假路径

## 10. 最佳实践

1. **分层分析**：先分析模块级，再分析顶层
2. **定期验证**：在综合、布局、布线各阶段都进行时序分析
3. **文档记录**：记录时序违例和修复方法
4. **回归测试**：确保修复不影响其他路径
5. **多角验证**：在所有工艺角下验证时序
6. **早期预警**：尽早发现和解决时序问题

## 11. 参考文档

- Synopsys PrimeTime User Guide
- Synopsys SolvNet知识库
- 时序约束编写指南
- 项目特定时序分析流程
