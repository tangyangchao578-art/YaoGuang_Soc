# Design Compiler综合最佳实践

## 概述

本文档提供Synopsys Design Compiler（DC）综合的最佳实践和优化技巧，帮助工程师获得最优的PPA（性能、功耗、面积）结果。

## 1. 综合前准备

### 1.1 设计检查清单

**RTL质量检查：**
- 所有模块必须可综合
- 无锁存器（Latch）
- 无组合环路
- 时钟域清晰
- 复位策略一致
- 异步处理（CDC）正确

**代码风格：**
- 使用参数化设计
- 避免X态传播
- 避免异步置位/复位混合使用
- 使用`always @ (posedge clk)`风格

### 1.2 库准备

**库文件需求：**
- 标准单元库（.lib/.db）
- 工艺库文件
- 约束文件（.sdc）

**库选择策略：**
- 综合时使用TT（Typical-Typical）库
- 时序分析时使用SS（Slow-Slow）和FF（Fast-Fast）库
- 根据应用温度选择对应的库

### 1.3 约束准备

**时钟约束：**
```tcl
# 时钟定义
create_clock -name clk -period 10 [get_ports clk]

# 时钟不确定性
set_clock_uncertainty -setup 0.5 [get_clocks clk]
set_clock_uncertainty -hold 0.1 [get_clocks clk]

# 时钟转换时间
set_clock_transition -rise 0.2 [get_clocks clk]
set_clock_transition -fall 0.2 [get_clocks clk]
```

**输入输出约束：**
```tcl
# 输入延迟
set_input_delay -clock clk -max 2.0 [get_ports data_in*]
set_input_delay -clock clk -min 0.5 [get_ports data_in*]

# 输出延迟
set_output_delay -clock clk -max 3.0 [get_ports data_out*]
set_output_delay -clock clk -min 1.0 [get_ports data_out*]

# 驱动单元
set_driving_cell -lib_cell INVX1 [get_ports data_in*]

# 输出负载
set_load 0.5 [get_ports data_out*]
```

## 2. 综合策略

### 2.1 基本综合流程

```tcl
# 1. 设置库
set_app_var target_library "tt_0p9v_25c.db"
set_app_var link_library "* $target_library"

# 2. 读取设计
read_verilog your_design.v
current_design your_design
link

# 3. 加载约束
read_sdc your_constraints.sdc

# 4. 综合前的检查
check_design
check_timing

# 5. 运行综合
compile_ultra

# 6. 综合后的检查
report_area
report_timing
report_constraint -all_violators
```

### 2.2 优化策略选择

**面积优化：**
```tcl
compile_ultra -area_high_effort_script

# 或分步优化
compile_ultra -no_autoungroup
compile_ultra -area_high_effort_script
```

**时序优化：**
```tcl
compile_ultra -timing_high_effort_script

# 或分步优化
compile_ultra -no_autoungroup
compile_ultra -timing_high_effort_script
```

**功耗优化：**
```tcl
compile_ultra -power_high_effort_script

# 或插入时钟门控
insert_clock_gating
compile_ultra -power_high_effort_script
```

**平衡优化：**
```tcl
compile_ultra
```

### 2.3 高级优化技巧

**逻辑重组：**
```tcl
# 启用逻辑重组
set_app_var restructure_design true
set_app_var restructure_timing true

# 或禁用逻辑重组
set_app_var restructure_design false
```

**资源共享：**
```tcl
# 启用资源共享
set_resource_implementation
area, high_speed, low_power
```

**状态机优化：**
```tcl
# 状态机编码
set_fsm_auto_state_encoding one_hot
set_fsm_onehot_state_encoding true
```

## 3. 时序优化技巧

### 3.1 关键路径识别

```tcl
# 报告关键路径
report_timing -max_paths 20

# 报告setup违例
report_timing -delay_type max -slack_lesser_than 0.1

# 报告hold违例
report_timing -delay_type min -slack_lesser_than 0.0
```

### 3.2 路径优化方法

**Setup优化：**
1. 增加驱动强度
   ```tcl
   resize_cell [get_cells inst_name] [get_lib_cells BUFFX4]
   ```

2. 插入缓冲器
   ```tcl
   insert_buffer [get_pins inst_name/Z] BUFFX2
   ```

3. 调整单元映射
   ```tcl
   set_app_var target_library "high_speed_lib.db"
   ```

4. 逻辑重构
   ```tcl
   # 重构关键路径逻辑
   compile_ultra -incremental
   ```

**Hold优化：**
1. 减小驱动强度
   ```tcl
   resize_cell [get_cells inst_name] [get_lib_cells BUFFX1]
   ```

2. 插入延迟单元
   ```tcl
   insert_buffer [get_pins inst_name/Z] DELAY_CELL
   ```

3. 调整时钟树
   ```tcl
   set_clock_latency -max 0.5 [get_clocks clk]
   ```

### 3.3 约束优化

**多周期路径：**
```tcl
# Setup多周期
set_multicycle_path -setup 2 -from [get_cells slow_reg*]

# Hold多周期
set_multicycle_path -hold 1 -from [get_cells slow_reg*]
```

**虚假路径：**
```tcl
# 测试模式路径
set_false_path -from [get_ports test_mode]

# 跨时钟域路径
set_false_path -from [get_clocks clk1] -to [get_clocks clk2]

# 复位路径
set_false_path -from [get_ports reset_n]
```

## 4. 面积优化技巧

### 4.1 单元映射优化

```tcl
# 使用最小单元
set_app_var target_library "area_lib.db"

# 或混合映射
set_app_var target_library "area_lib.db speed_lib.db"
```

### 4.2 资源共享

```tcl
# 启用资源共享
set_resource_implementation area
set_app_var compile_area_high_effort true
```

### 4.3 逻辑优化

```tcl
# 逻辑优化
optimize_design -area

# 或逻辑重构
compile_ultra -area_high_effort_script
```

## 5. 功耗优化技巧

### 5.1 时钟门控

```tcl
# 识别门控候选
identify_clock_gating_elements

# 插入门控时钟
insert_clock_gating

# 门控时钟优化
compile_ultra -power_high_effort_script
```

### 5.2 数据门控

```tcl
# 手动添加数据门控逻辑
# 在RTL中使用enable信号控制数据通路
```

### 5.3 多阈值电压

```tcl
# 使用多Vt单元
set_app_var target_library "svt_lib.db lvt_lib.db hvt_lib.db"

# 设置默认Vt
set_app_var default_threshold_voltage_group SVT
```

## 6. 综合后验证

### 6.1 基本检查

```tcl
# 设计检查
check_design > design_check.rpt

# 时序检查
check_timing > timing_check.rpt

# 约束检查
report_constraint -all_violators > constraint_violations.rpt
```

### 6.2 详细分析

```tcl
# 面积报告
report_area -hierarchy > area.rpt

# 时序报告
report_timing -max_paths 10 > timing.rpt

# QOR报告
report_qor > qor.rpt

# 资源报告
report_resources > resources.rpt
```

### 6.3 功耗分析

```tcl
# 读取活动文件
read_saif -input your_design.saif -instance root

# 功耗报告
report_power -hierarchy > power.rpt

# 泄漏功耗
report_power -leakage > leakage.rpt

# 动态功耗
report_power -dynamic > dynamic.rpt
```

## 7. 常见问题和解决方案

### 7.1 综合失败

**问题：** link失败
- 检查库路径
- 检查缺失的模块
- 验证库版本兼容性

**问题：** 综合后网表与RTL不匹配
- 检查RTL编码风格
- 验证综合约束
- 使用`verify_rtl_netlist`验证

### 7.2 时序不满足

**问题：** Setup违例
- 增加时钟周期（如果可能）
- 优化关键路径
- 使用时序约束优化
- 考虑流水线插入

**问题：** Hold违例
- 插入延迟单元
- 调整时钟树
- 优化路径平衡

### 7.3 面积过大

**问题：** 面积超出预算
- 使用面积优化脚本
- 优化单元映射
- 启用资源共享
- 检查不必要的逻辑

### 7.4 DRC违例

**问题：** 最大扇出违例
- 插入缓冲器
- 分割高扇出网络

**问题：** 最大转换时间违例
- 增加驱动强度
- 优化负载

**问题：** 最大电容违例
- 减小负载
- 增加驱动能力

## 8. 综合质量检查清单

### 8.1 综合前检查
- [ ] RTL代码完成并通过lint检查
- [ ] 所有模块可综合
- [ ] 时钟约束完整
- [ ] 输入输出约束合理
- [ ] 库文件正确加载
- [ ] 设计可link

### 8.2 综合后检查
- [ ] 时序满足要求（setup/hold）
- [ ] 面积在预算内
- [ ] DRC无违例
- [ ] 功耗满足要求
- [ ] 网表与RTL功能一致
- [ ] 所有约束被尊重
- [ ] 无未使用的端口
- [ ] 无浮空网络

### 8.3 输出文件检查
- [ ] 网表文件（.v/.ddc）
- [ ] 约束文件（.sdc）
- [ ] 报告文件完整
- [ ] 寄生参数文件（.spef）
- [ ] 时序报告正确

## 9. 最佳实践总结

1. **约束优先**：确保约束完整且合理
2. **迭代优化**：综合-分析-优化循环
3. **PPA平衡**：根据项目需求平衡性能、功耗、面积
4. **早期验证**：尽早发现和解决问题
5. **文档记录**：记录综合决策和结果
6. **回归测试**：确保修改不影响已通过的模块

## 10. 参考文档

- Synopsys Design Compiler User Guide
- Synopsys SolvNet知识库
- 工艺库文档
- 项目特定综合指南
