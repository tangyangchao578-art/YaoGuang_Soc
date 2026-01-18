# Display Subsystem SDC (Synopsys Design Constraints)

**Document Version**: v1.0  
**Created Date**: 2026-01-18  
**Module**: Display Subsystem  
**Status**: Draft

---

## 1. 时钟定义

### 1.1 基础时钟

```tcl
# System Clock (from NoC)
create_clock -name clk_sys -period 5.0 [get_ports clk_sys]
set_clock_uncertainty -setup 0.2 clk_sys
set_clock_uncertainty -hold 0.1 clk_sys

# Pixel Clock (dynamic, default 148.5MHz for 1080p@60Hz)
create_clock -name pixel_clk -period 6.73 [get_ports pixel_clk]
set_clock_uncertainty -setup 0.1 pixel_clk
set_clock_uncertainty -hold 0.05 pixel_clk

# AXI Clock (from NoC)
create_clock -name axi_clk -period 5.0 [get_clocks clk_sys]
```

### 1.2 派生时钟

```tcl
# Generated clocks for serializers
derive_pll_clocks -create_added_clocks
derive_clock_uncertainty
```

### 1.3 时钟组

```tcl
# Asynchronous clock groups
set_clock_groups -asynchronous \
    -group {clk_sys} \
    -group {pixel_clk}
```

---

## 2. 输入输出延迟

### 2.1 输出延迟

```tcl
# HDMI Interface Output Delays
set_output_delay -clock pixel_clk -max 0.5 [get_ports hdmi_tx_clk_p]
set_output_delay -clock pixel_clk -min -0.3 [get_ports hdmi_tx_clk_p]
set_output_delay -clock pixel_clk -max 0.5 [get_ports {hdmi_tx_data_p[*]}]
set_output_delay -clock pixel_clk -min -0.3 [get_ports {hdmi_tx_data_p[*]}]

# DisplayPort Interface Output Delays
set_output_delay -clock pixel_clk -max 0.5 [get_ports dp_tx_clk_p]
set_output_delay -clock pixel_clk -min -0.3 [get_ports dp_tx_clk_p]
set_output_delay -clock pixel_clk -max 0.5 [get_ports {dp_tx_data_p[*]}]
set_output_delay -clock pixel_clk -min -0.3 [get_ports {dp_tx_data_p[*]}]

# MIPI DSI Interface Output Delays
set_output_delay -clock pixel_clk -max 0.3 [get_ports dsi_clk_p]
set_output_delay -clock pixel_clk -min -0.2 [get_ports dsi_clk_p]
set_output_delay -clock pixel_clk -max 0.3 [get_ports {dsi_data_p[*]}]
set_output_delay -clock pixel_clk -min -0.2 [get_ports {dsi_data_p[*]}]
```

### 2.2 输入延迟

```tcl
# HPD Inputs
set_input_delay -clock pixel_clk -max 1.0 [get_ports hdmi_hpd]
set_input_delay -clock pixel_clk -min 0.0 [get_ports hdmi_hpd]
set_input_delay -clock pixel_clk -max 1.0 [get_ports dp_hpd]
set_input_delay -clock pixel_clk -min 0.0 [get_ports dp_hpd]
set_input_delay -clock pixel_clk -max 1.0 [get_ports dsi_te]
set_input_delay -clock pixel_clk -min 0.0 [get_ports dsi_te]
```

---

## 3. 负载模型

### 3.1 输出负载

```tcl
# HDMI TMDS loads (approximate)
set_load -pin_load 0.05 [get_ports hdmi_tx_clk_p]
set_load -pin_load 0.05 [get_ports hdmi_tx_clk_n]
set_load -pin_load 0.05 [get_ports {hdmi_tx_data_p[*]}]
set_load -pin_load 0.05 [get_ports {hdmi_tx_data_n[*]}]

# DisplayPort LVDS loads
set_load -pin_load 0.05 [get_ports dp_tx_clk_p]
set_load -pin_load 0.05 [get_ports dp_tx_clk_n]
set_load -pin_load 0.05 [get_ports {dp_tx_data_p[*]}]
set_load -pin_load 0.05 [get_ports {dp_tx_data_n[*]}]

# MIPI D-PHY loads
set_load -pin_load 0.03 [get_ports dsi_clk_p]
set_load -pin_load 0.03 [get_ports dsi_clk_n]
set_load -pin_load 0.03 [get_ports {dsi_data_p[*]}]
set_load -pin_load 0.03 [get_ports {dsi_data_n[*]}]
```

---

## 4. 驱动强度

```tcl
# Output drive strengths
set_drive -cell AND2X1 -rise 0.5 [get_ports {s_awready s_wready s_arready s_rvalid s_bvalid}]
set_drive -cell AND2X1 -fall 0.5 [get_ports {s_awready s_wready s_arready s_rvalid s_bvalid}]

# Reset and control signals
set_drive -cell BUF_X4 -rise 2.0 [get_ports rst_n]
set_drive -cell BUF_X4 -fall 2.0 [get_ports rst_n]
```

---

## 5. 多周期路径

### 5.1 像素数据通路

```tcl
# Pixel data pipeline has 5 stages
set_multicycle_path -setup -from [get_pixels -of_objects [get_registers pixel_data_r*]] \
    -to [get_pixels -of_objects [get_registers out_data_r*]] 5
set_multicycle_path -hold -from [get_pixels -of_objects [get_registers pixel_data_r*]] \
    -to [get_pixels -of_objects [get_registers out_data_r*]] 4
```

### 5.2 AXI 读写路径

```tcl
# AXI response path
set_multicycle_path -setup -from [get_registers -filter {name =~ *axi*} -clock clk_sys] \
    -to [get_pixels -of_objects [get_registers s_rdata*]] 2
set_multicycle_path -hold -from [get_registers -filter {name =~ *axi*} -clock clk_sys] \
    -to [get_pixels -of_objects [get_registers s_rdata*]] 1
```

---

## 6. 伪路径

### 6.1 异步复位同步释放

```tcl
# Async reset synchronization
set_false_path -from [get_ports rst_n]
```

### 6.2 跨时钟域路径

```tcl
# Clock domain crossing paths
set_false_path -from [get_clocks clk_sys] -to [get_clocks pixel_clk]
set_false_path -from [get_clocks pixel_clk] -to [get_clocks clk_sys]
```

### 6.3 三态信号

```tcl
# Bidirectional signals
set_false_path -from [get_ports hdmi_cec]
set_false_path -from [get_ports {dp_aux_p dp_aux_n}]
```

---

## 7. 最大过渡时间

```tcl
# Output transition limits
set_max_transition 0.5 [get_ports {hdmi_tx_clk_p hdmi_tx_clk_n hdmi_tx_data_p[*] hdmi_tx_data_n[*]}]
set_max_transition 0.5 [get_ports {dp_tx_clk_p dp_tx_clk_n dp_tx_data_p[*] dp_tx_data_n[*]}]
set_max_transition 0.3 [get_ports {dsi_clk_p dsi_clk_n dsi_data_p[*] dsi_data_n[*]}]

# Control signal transition limits
set_max_transition 1.0 [get_ports {s_awready s_wready s_arready s_rvalid s_bvalid int_display}]
```

---

## 8. 面积约束

```tcl
# Target area
set_max_area 200000  # 200K um^2 estimated
```

---

## 9. 功耗约束

```tcl
# Power optimization
set_power_optimization -verbose true
set_max_dynamic_power 500  # mW
set_leakage_power_constraint 50  # mW
```

---

## 10. 时序异常

### 10.1 关键路径异常

```tcl
# TMDS serializer critical path
set_max_delay -from [get_registers -filter {name =~ *tmds_enc*}] \
    -to [get_registers -filter {name =~ *tmds_ser*}] -0.5
```

### 10.2 寄存器复位路径

```tcl
# Reset to Q delay
set_max_delay -from [get_ports rst_n] -to [get_registers -filter {name =~ *rst*}] 2.0
```

---

## 11. 寄存器类型设置

```tcl
# Don't touch registers
set_dont_touch [get_registers -filter {name =~ *pixel_clk* && name =~ *reg*}]

# Runtime optimization registers
set_register_type -element [get_registers -filter {name =~ *pipeline*}] -type high_speed
```

---

## 12. 设计规则检查

```tcl
# Enable DRC
set_drc_effort high

# Max fanout
set_max_fanout 32 [get_design display_top]

# Min pulse width
set_min_pulse_width -clock pixel_clk 0.5
```

---

## 13. 优化设置

```tcl
# Timing-driven placement
set_app_var place_opt_effort high

# Clock gate optimization
set_clock_gating_check -setup 0.1 -hold 0.05

# DSP and RAM utilization
set_max_utilization -type dsp 80
set_max_utilization -type ram 80
```

---

## 文档版本历史

| 版本 | 日期 | 作者 | 变更说明 |
|------|------|------|----------|
| v1.0 | 2026-01-18 | YaoGuang Arch Team | 初始版本 |
