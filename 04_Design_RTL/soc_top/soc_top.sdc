# YaoGuang SoC Top-Level SDC 约束文件

## 文件信息

| 项目 | 内容 |
|------|------|
| **文件名** | soc_top.sdc |
| **版本** | V1.0 |
| **创建日期** | 2026-01-18 |
| **适用工艺** | TSMC 7nm FinFET |
| **目标频率** | 2.0 GHz |

---

## 1. 时钟定义

### 1.1 主时钟

```tcl
# 主晶振输入 (24 MHz)
create_clock -period 41.6667 -name osc_24mhz [get_ports osc_24mhz]

# RTC 晶振输入 (32.768 kHz)
create_clock -period 30517.578 -name osc_32k [get_ports osc_32k]

# DDR PHY 时钟
create_clock -period 0.625 -name ddr_phy_clk [get_ports ddr_phy_clk_p]
```

### 1.2 PLL 输出时钟

```tcl
# CPU/NPU/GPU 时钟 (2.0 GHz)
create_clock -period 0.5 -name clk_core [get_pins -hierarchical -filter name=~clk_core]
create_clock -period 0.5 -name clk_npu [get_pins -hierarchical -filter name=~clk_npu]

# GPU 时钟 (1.5 GHz)
create_clock -period 0.6667 -name clk_gpu [get_pins -hierarchical -filter name=~clk_gpu]

# ISP 时钟 (800 MHz)
create_clock -period 1.25 -name clk_isp [get_pins -hierarchical -filter name=~clk_isp]

# NoC 时钟 (2.0 GHz)
create_clock -period 0.5 -name clk_noc [get_pins -hierarchical -filter name=~clk_noc]

# DDR 控制器时钟 (1.6 GHz)
create_clock -period 0.625 -name clk_mem [get_pins -hierarchical -filter name=~clk_mem]

# 系统时钟 (500 MHz)
create_clock -period 2.0 -name clk_sys [get_pins -hierarchical -filter name=~clk_sys]

# USB 时钟 (480 MHz)
create_clock -period 2.0833 -name clk_usb [get_pins -hierarchical -filter name=~clk_usb]

# PCIe 时钟 (250 MHz)
create_clock -period 4.0 -name clk_pcie [get_pins -hierarchical -filter name=~clk_pcie]

# Ethernet 时钟 (312.5 MHz)
create_clock -period 3.2 -name clk_eth [get_pins -hierarchical -filter name=~clk_eth]
```

### 1.3 时钟组约束

```tcl
# 异步时钟组
set_clock_groups -asynchronous \
    -group [get_clocks clk_core] \
    -group [get_clocks clk_npu] \
    -group [get_clocks clk_gpu] \
    -group [get_clocks clk_isp] \
    -group [get_clocks clk_noc] \
    -group [get_clocks clk_mem] \
    -group [get_clocks clk_sys] \
    -group [get_clocks clk_usb] \
    -group [get_clocks clk_pcie] \
    -group [get_clocks clk_eth]

# DDR PHY 时钟组
set_clock_groups -asynchronous \
    -group [get_clocks clk_mem] \
    -group [get_clocks ddr_phy_clk]
```

### 1.4 时钟抖动约束

```tcl
# 时钟抖动
set_clock_uncertainty -setup 0.05 [get_clocks clk_core]
set_clock_uncertainty -setup 0.05 [get_clocks clk_npu]
set_clock_uncertainty -setup 0.05 [get_clocks clk_noc]
set_clock_uncertainty -setup 0.03 [get_clocks clk_mem]
set_clock_uncertainty -setup 0.03 [get_clocks clk_sys]

set_clock_uncertainty -hold 0.02 [get_clocks clk_core]
set_clock_uncertainty -hold 0.02 [get_clocks clk_npu]
set_clock_uncertainty -hold 0.02 [get_clocks clk_noc]
```

---

## 2. 复位定义

### 2.1 复位端口

```tcl
# 复位端口
set_reset_ports [list por_n ext_rst_n jtag_trst_n]
```

### 2.2 复位路径约束

```tcl
# 复位恢复时间
set_resetRecovery -setup 0.1 [get_ports por_n]
set_resetRecovery -setup 0.1 [get_ports ext_rst_n]
set_resetRecovery -hold 0.05 [get_ports por_n]
set_resetRecovery -hold 0.05 [get_ports ext_rst_n]
```

---

## 3. IO 约束

### 3.1 输入延迟

```tcl
# DDR DQ 输入延迟
set_input_delay -clock clk_mem -max 0.3 [get_ports ddr_dq_p*]
set_input_delay -clock clk_mem -min -0.1 [get_ports ddr_dq_p*]

# DDR DQS 输入延迟
set_input_delay -clock clk_mem -max 0.25 [get_ports ddr_dqs_p*]
set_input_delay -clock clk_mem -min -0.05 [get_ports ddr_dqs_p*]

# GPIO 输入延迟
set_input_delay -clock clk_sys -max 2.0 [get_ports gpio*]
set_input_delay -clock clk_sys -min 0.5 [get_ports gpio*]

# UART 输入延迟
set_input_delay -clock clk_sys -max 10.0 [get_ports uart_rx*]
set_input_delay -clock clk_sys -min 2.0 [get_ports uart_rx*]

# JTAG 输入延迟
set_input_delay -clock jtag_tck -max 5.0 [get_ports jtag_tms jtag_tdi]
set_input_delay -clock jtag_tck -min 1.0 [get_ports jtag_tms jtag_tdi]
```

### 3.2 输出延迟

```tcl
# DDR DQ 输出延迟
set_output_delay -clock clk_mem -max 0.3 [get_ports ddr_dq_p*]
set_output_delay -clock clk_mem -min -0.1 [get_ports ddr_dq_p*]

# DDR DQS 输出延迟
set_output_delay -clock clk_mem -max 0.25 [get_ports ddr_dqs_p*]
set_output_delay -clock clk_mem -min -0.05 [get_ports ddr_dqs_p*]

# GPIO 输出延迟
set_output_delay -clock clk_sys -max 2.0 [get_ports gpio*]
set_output_delay -clock clk_sys -min 0.5 [get_ports gpio*]

# UART 输出延迟
set_output_delay -clock clk_sys -max 10.0 [get_ports uart_tx*]
set_output_delay -clock clk_sys -min 2.0 [get_ports uart_tx*]

# JTAG 输出延迟
set_output_delay -clock jtag_tck -max 5.0 [get_ports jtag_tdo]
set_output_delay -clock jtag_tck -min 1.0 [get_ports jtag_tdo]
```

### 3.3 驱动强度与负载

```tcl
# IO 标准
set_io_standard -name LVCMOS18 [get_ports gpio*]
set_io_standard -name LVCMOS18 [get_ports uart_*]
set_io_standard -name LVCMOS18 [get_ports i2c_*]
set_io_standard -name LVCMOS18 [get_ports spi_*]
set_io_standard -name LVDS [get_ports ddr_dq_p*]
set_io_standard -name LVDS [get_ports ddr_dqs_p*]

# 驱动强度
set_driving_cell -lib_cell buf_4 [get_ports gpio*]
set_driving_cell -lib_cell buf_2 [get_ports uart_*]
set_driving_cell -lib_cell buf_2 [get_ports i2c_*]
set_driving_cell -lib_cell buf_4 [get_ports spi_*]
```

---

## 4. 时序异常

### 4.1 虚假路径

```tcl
# 异步复位路径
set_false_path -from [get_ports por_n] -to [get_pins */rst_n]
set_false_path -from [get_ports ext_rst_n] -to [get_pins */rst_n]

# 调试接口
set_false_path -from [get_ports jtag_tck] -to [get_pins */jtag*]
set_false_path -from [get_pins */jtag*] -to [get_ports jtag_tdo]

# 慢速外设
set_false_path -from [get_clocks clk_sys] -to [get_pins i2c_*/clk]
set_false_path -from [get_clocks clk_sys] -to [get_pins spi_*/clk]

# RTC 时钟域
set_false_path -from [get_clocks osc_32k] -to [get_clocks clk_sys]
set_false_path -from [get_clocks clk_sys] -to [get_clocks osc_32k]
```

### 4.2 多周期路径

```tcl
# 异步 FIFO 读写
set_multicycle_path -setup 2 -from [get_clocks clk_mem] -to [get_clocks clk_sys]
set_multicycle_path -hold 1 -from [get_clocks clk_mem] -to [get_clocks clk_sys]

# APB 寄存器访问
set_multicycle_path -setup 2 -from [get_clocks clk_sys] -to [get_pins apb_*/pclk]
set_multicycle_path -hold 1 -from [get_clocks clk_sys] -to [get_pins apb_*/pclk]

# 慢速外设寄存器
set_multicycle_path -setup 10 -from [get_clocks clk_sys] -to [get_pins i2c_*/clk]
set_multicycle_path -hold 9 -from [get_clocks clk_sys] -to [get_pins i2c_*/clk]
```

### 4.3 最大延迟

```tcl
# 关键路径最大延迟
set_max_delay -from [get_pins */clk] -to [get_pins */rst_n] 5.0
set_max_delay -from [get_ports por_n] -to [get_pins */rst_n] 10.0
```

---

## 5. 负载模型

### 5.1 估计负载

```tcl
# 估计输出负载
set_load -pin_load 0.005 [get_ports gpio*]
set_load -pin_load 0.01 [get_ports uart_*]
set_load -pin_load 0.002 [get_ports i2c_*]
set_load -pin_load 0.005 [get_ports spi_*]
set_load -pin_load 0.05 [get_ports ddr_dq_p*]
set_load -pin_load 0.05 [get_ports ddr_dqs_p*]
```

### 5.2 IO 负载

```tcl
# DDR IO 负载
set_load 0.1 [get_ports ddr_dq_p*]
set_load 0.1 [get_ports ddr_dqs_p*]
set_load 0.05 [get_ports ddr_a*]
set_load 0.05 [get_ports ddr_cs_n*]
```

---

## 6. 面积约束

```tcl
# 面积目标
set_max_area 120000000  # 120 mm² in µm²
```

---

## 7. 功耗约束

### 7.1 功耗预算

```tcl
# 动态功耗预算
set_max_dynamic_power 60.0
set_max_leakage_power 5.0
```

### 7.2 开关活动

```tcl
# 默认开关活动
set_switching_activity -default_toggle_rate 0.2
set_switching_activity -default_static_probability 0.5
```

---

## 8. 时钟门控约束

```tcl
# 时钟门控检查
set_clock_gating_check -setup 0.1
set_clock_gating_check -hold 0.05
```

---

## 9. 关键端口约束

### 9.1 启动模式

```tcl
# 启动模式引脚
set_load -pin_load 0.01 [get_ports boot_mode*]
set_driving_cell -lib_cell buf_2 [get_ports boot_mode*]
```

### 9.2 状态指示

```tcl
# LED 状态引脚
set_load -pin_load 0.01 [get_ports led_status]
set_load -pin_load 0.01 [get_ports led_error]
set_driving_cell -lib_cell buf_1 [get_ports led_status]
set_driving_cell -lib_cell buf_1 [get_ports led_error]
```

---

## 10. 设计与库设置

### 10.1 目标库

```tcl
# 目标标准单元库
set_target_library { * }
set_link_library { * }
```

### 10.2 设计约束

```tcl
# 设计名称
current_design soc_top

# 单位
set_units time ns
set_units capacitance fF
set_units resistance kOhm
set_units voltage V
set_units current mA
```

---

## 11. 报告设置

### 11.1 时序报告

```tcl
# 时序报告选项
report_timing -delay_type max -max_paths 10 -sort_by group
report_clock_timing -type skew
report_clock_timing -type uncertainty
```

### 11.2 面积报告

```tcl
report_area -hierarchical
report_cell
```

### 11.3 功耗报告

```tcl
report_power -hierarchical
report_switching_activity
```

---

## 12. 验收标准

| 检查项 | 目标值 | 备注 |
|--------|--------|------|
| **时钟频率** | 2.0 GHz | CPU/NPU/NoC |
| **Setup Slack** | > 0 ns | 所有时序路径 |
| **Hold Slack** | > 0 ns | 所有时序路径 |
| **面积** | < 120 mm² | 包含所有模块 |
| **动态功耗** | < 60 W | 典型工作负载 |
| **静态功耗** | < 5 W | 待机状态 |

---

## 审批

| 角色 | 姓名 | 签名 | 日期 |
|------|------|------|------|
| 时序工程师 | - | - | - |
| 后端工程师 | - | - | - |
| 架构师 | - | - | - |

---

**文档版本**: V1.0  
**创建日期**: 2026-01-18  
**最后更新**: 2026-01-18

---

*本约束文件用于 SoC 顶层时序分析与优化。*
