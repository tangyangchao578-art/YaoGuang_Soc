# ============================================================================
# File: l3_cache.sdc
# Description: L3 Cache时序约束文件
# Version: 1.0
# Date: 2026-01-18
# ============================================================================

# ============================================================================
# 1. 时钟定义
# ============================================================================

# 主时钟
create_clock -name clk_l3 -period 0.667 [get_ports clk]
set_clock_uncertainty 0.05 clk_l3
set_clock_transition 0.05 clk_l3

# PLL时钟（如果使用）
# create_clock -name clk_pll -period 0.667 [get_pins PLL_inst/CLKOUT]

# ============================================================================
# 2. 时钟组
# ============================================================================

# 所有AXI接口使用同一时钟
set_clock_groups -asynchronous \
    -group {clk_l3} \
    -group {clk}

# ============================================================================
# 3. 输入延迟约束
# ============================================================================

# 从接口（Master连接）输入延迟
set_input_delay -clock clk_l3 -max 0.3 \
    [get_ports {saxi_arvalid[*] saxi_awvalid[*] saxi_wvalid[*]}] \
    -group clk_l3

set_input_delay -clock clk_l3 -max 0.3 \
    [get_ports {saxi_araddr[*] saxi_awaddr[*]}] \
    -group clk_l3

set_input_delay -clock clk_l3 -max 0.3 \
    [get_ports {saxi_arlen[*] saxi_awlen[*] saxi_arsize[*] saxi_awsize[*]}] \
    -group clk_l3

set_input_delay -clock clk_l3 -max 0.3 \
    [get_ports {saxi_wdata[*] saxi_wstrb[*]}] \
    -group clk_l3

# 主接口输入延迟（NoC响应）
set_input_delay -clock clk_l3 -max 0.4 \
    [get_ports {maxi_arready maxi_awready maxi_rvalid maxi_bvalid}] \
    -group clk_l3

set_input_delay -clock clk_l3 -max 0.4 \
    [get_ports {maxi_rdata maxi_rresp maxi_bresp maxi_rlast}] \
    -group clk_l3

# 复位输入
set_input_delay -clock clk_l3 -max 1.0 [get_ports rst_n] -group clk_l3

# ============================================================================
# 4. 输出延迟约束
# ============================================================================

# 从接口输出延迟
set_output_delay -clock clk_l3 -max 0.3 \
    [get_ports {saxi_arready[*] saxi_awready[*] saxi_wready[*]}] \
    -group clk_l3

set_output_delay -clock clk_l3 -max 0.3 \
    [get_ports {saxi_rvalid[*] saxi_bvalid[*] saxi_rlast[*]}] \
    -group clk_l3

set_output_delay -clock clk_l3 -max 0.3 \
    [get_ports {saxi_rdata[*] saxi_rresp[*] saxi_bresp[*]}] \
    -group clk_l3

# 主接口输出延迟（NoC请求）
set_output_delay -clock clk_l3 -max 0.4 \
    [get_ports {maxi_arvalid maxi_awvalid maxi_wvalid maxi_rready maxi_bready}] \
    -group clk_l3

set_output_delay -clock clk_l3 -max 0.4 \
    [get_ports {maxi_araddr maxi_awaddr maxi_arlen maxi_awlen maxi_arsize maxi_awsize}] \
    -group clk_l3

set_output_delay -clock clk_l3 -max 0.4 \
    [get_ports {maxi_wdata maxi_wstrb maxi_wlast}] \
    -group clk_l3

# ============================================================================
# 5. 多周期路径约束
# ============================================================================

# AXI通道内READY/VALID握手
set_multicycle_path -setup 2 \
    -from [get_pins -hierarchical {*saxi_arvalid*}] \
    -to [get_pins -hierarchical {*saxi_arready*}] \
    -group clk_l3

set_multicycle_path -setup 2 \
    -from [get_pins -hierarchical {*saxi_awvalid*}] \
    -to [get_pins -hierarchical {*saxi_awready*}] \
    -group clk_l3

set_multicycle_path -setup 2 \
    -from [get_pins -hierarchical {*saxi_wvalid*}] \
    -to [get_pins -hierarchical {*saxi_wready*}] \
    -group clk_l3

set_multicycle_path -setup 2 \
    -from [get_pins -hierarchical {*saxi_rvalid*}] \
    -to [get_pins -hierarchical {*saxi_rready*}] \
    -group clk_l3

set_multicycle_path -setup 2 \
    -from [get_pins -hierarchical {*saxi_bvalid*}] \
    -to [get_pins -hierarchical {*saxi_bready*}] \
    -group clk_l3

# SRAM读路径（1周期延迟）
set_multicycle_path -setup 1 \
    -from [get_pins -hierarchical {*tag_sram*CLK}] \
    -to [get_pins -hierarchical {*tag_hit*REG*}] \
    -group clk_l3

set_multicycle_path -setup 1 \
    -from [get_pins -hierarchical {*data_sram*CLK}] \
    -to [get_pins -hierarchical {*data_read_data*REG*}] \
    -group clk_l3

# ============================================================================
# 6. 虚假路径约束
# ============================================================================

# 测试和调试端口
set_false_path -from [get_ports {test_*}]
set_false_path -to [get_ports {test_*}]

# 配置寄存器（软件可配置）
set_false_path -from [get_ports {cfg_*}]
set_false_path -to [get_ports {cfg_*}]

# 状态和统计输出
set_false_path -from [get_ports {cache_status hit_count miss_count flush_done}]

# 异步复位
set_false_path -from [get_ports rst_n]

# ============================================================================
# 7. 最大过渡时间约束
# ============================================================================

set_max_transition 0.2 [current_design]
set_max_fanout 20 [current_design]

# ============================================================================
# 8. 驱动强度约束
# ============================================================================

set_drive 0.1 [get_ports {saxi_*} {maxi_*}]
set_load -pin_load 0.05 [get_ports {saxi_*} {maxi_*}]

# ============================================================================
# 9. 面积约束
# ============================================================================

set_max_area 6000000  # 6 mm²

# ============================================================================
# 10. 功耗约束
# ============================================================================

set_power_estimation -mode on_chip
set_max_dynamic_power 3000  # 3W

# ============================================================================
# 11. 关键路径异常
# ============================================================================

# Tag比较路径（关键路径）
set_max_delay -from [get_pins u_tag_array/read_path*/tag_sram*CLK] \
              -to [get_pins u_request_handler/tag_hit*REG*/D] \
              0.8 -group clk_l3

# Data选择路径
set_max_delay -from [get_pins u_data_array/read_path*/data_sram*CLK] \
              -to [get_pins u_request_handler/data_read_data*REG*/D] \
              0.8 -group clk_l3

# ============================================================================
# 12. 边界约束
# ============================================================================

set_operating_conditions -max tt_125 -min ff_n40
set_voltage 0.9 -nominal_voltage 0.8 -max_voltage 1.0 -min_voltage 0.7
