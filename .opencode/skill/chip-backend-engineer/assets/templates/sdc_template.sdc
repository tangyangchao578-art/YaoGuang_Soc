# ============================================================================
# SDC约束文件模板
# Synopsys Design Constraints
# ============================================================================

# ============================================================================
# 1. 时钟定义
# ============================================================================

# 主时钟
create_clock -name clk -period 10.0 [get_ports clk]

# 时钟不确定性（工艺、电压、温度变化）
set_clock_uncertainty -setup 0.5 [get_clocks clk]
set_clock_uncertainty -hold 0.1 [get_clocks clk]

# 时钟转换时间（上升/下降）
set_clock_transition -rise 0.2 [get_clocks clk]
set_clock_transition -fall 0.2 [get_clocks clk]

# 时钟延迟（可选，如果时钟网络延迟已知）
set_clock_latency -source 0.5 [get_clocks clk]
set_clock_latency 0.5 [get_clocks clk]

# 时钟skew（如果时钟树已经存在）
set_clock_skew -ideal [get_clocks clk]

# ============================================================================
# 2. 多时钟定义（如果设计有多个时钟）
# ============================================================================

# 示例：系统时钟
create_clock -name sys_clk -period 8.0 [get_ports sys_clk]
set_clock_uncertainty -setup 0.4 [get_clocks sys_clk]
set_clock_uncertainty -hold 0.08 [get_clocks sys_clk]
set_clock_transition -rise 0.15 [get_clocks sys_clk]
set_clock_transition -fall 0.15 [get_clocks sys_clk]

# 示例：外设时钟（较慢）
create_clock -name per_clk -period 25.0 [get_ports per_clk]
set_clock_uncertainty -setup 0.8 [get_clocks per_clk]
set_clock_uncertainty -hold 0.15 [get_clocks per_clk]
set_clock_transition -rise 0.3 [get_clocks per_clk]
set_clock_transition -fall 0.3 [get_clocks per_clk]

# 时钟组（如果时钟不相关）
# set_clock_groups -asynchronous -group {clk} -group {sys_clk} -group {per_clk}

# 或逻辑相关
# set_clock_groups -logically_exclusive -group {clk} -group {sys_clk}

# ============================================================================
# 3. 生成时钟（如果有时钟分频器）
# ============================================================================

# 示例：分频时钟
create_generated_clock -name clk_div2 \
  -source [get_pins clk_div2_reg/Q] \
  -divide_by 2 \
  [get_ports clk_div2]

# ============================================================================
# 4. 输入延迟约束
# ============================================================================

# 输入端口示例
# 根据实际设计修改端口名称和延迟值

# 数据输入端口
set_input_delay -clock clk -max 2.0 [get_ports data_in*]
set_input_delay -clock clk -min 0.5 [get_ports data_in*]

# 地址输入端口
set_input_delay -clock clk -max 1.5 [get_ports addr_in*]
set_input_delay -clock clk -min 0.3 [get_ports addr_in*]

# 控制信号
set_input_delay -clock clk -max 1.0 [get_ports write_enable]
set_input_delay -clock clk -min 0.2 [get_ports write_enable]

# 复位信号（通常异步）
set_input_delay -clock clk -max 5.0 [get_ports reset_n]
set_input_delay -clock clk -min 0.0 [get_ports reset_n]

# ============================================================================
# 5. 输出延迟约束
# ============================================================================

# 输出端口示例
# 根据实际设计修改端口名称和延迟值

# 数据输出端口
set_output_delay -clock clk -max 3.0 [get_ports data_out*]
set_output_delay -clock clk -min 1.0 [get_ports data_out*]

# 状态输出端口
set_output_delay -clock clk -max 2.0 [get_ports status_out]
set_output_delay -clock clk -min 0.5 [get_ports status_out]

# 中断输出端口
set_output_delay -clock clk -max 4.0 [get_ports interrupt]
set_output_delay -clock clk -min 1.5 [get_ports interrupt]

# ============================================================================
# 6. 驱动单元约束
# ============================================================================

# 输入端口驱动强度
# 根据实际库文件修改单元名称

# 数据输入端口
set_driving_cell -lib_cell INVX1 [get_ports data_in*]

# 地址输入端口
set_driving_cell -lib_cell BUFFX2 [get_ports addr_in*]

# 控制信号
set_driving_cell -lib_cell INVX1 [get_ports write_enable]

# 复位信号（通常驱动能力较强）
set_driving_cell -lib_cell BUFFX4 [get_ports reset_n]

# 或直接设置驱动电阻
# set_input_transition -max 0.3 [get_ports data_in*]
# set_input_transition -min 0.1 [get_ports data_in*]

# ============================================================================
# 7. 输出负载约束
# ============================================================================

# 输出端口负载电容
# 单位：pF

# 数据输出端口
set_load 0.5 [get_ports data_out*]

# 状态输出端口
set_load 0.2 [get_ports status_out]

# 中断输出端口
set_load 0.3 [get_ports interrupt]

# ============================================================================
# 8. 虚假路径约束
# ============================================================================

# 测试模式端口（通常不进行时序分析）
set_false_path -from [get_ports test_mode]

# 复位信号（异步复位）
set_false_path -from [get_ports reset_n]

# 跨时钟域路径（需要单独处理）
# set_false_path -from [get_clocks clk] -to [get_clocks per_clk]
# set_false_path -from [get_clocks per_clk] -to [get_clocks clk]

# 配置寄存器（不常访问）
# set_false_path -to [get_cells config_reg*]

# ============================================================================
# 9. 多周期路径约束
# ============================================================================

# Setup多周期路径
# 示例：2个时钟周期完成的操作
# set_multicycle_path -setup 2 -from [get_cells slow_path_reg*]

# Hold多周期路径
# set_multicycle_path -hold 1 -from [get_cells slow_path_reg*]

# 示例：从输入到寄存器的多周期路径
# set_multicycle_path -setup 2 -from [get_ports data_in*] -to [get_registers]

# 示例：读操作多周期路径
# set_multicycle_path -setup 2 -through [get_cells read_fsm*]

# ============================================================================
# 10. 最大/最小延迟约束
# ============================================================================

# 组合逻辑最大延迟
# set_max_delay 5.0 -from [get_ports data_in*] -to [get_ports data_out*]

# 组合逻辑最小延迟
# set_min_delay 1.0 -from [get_ports data_in*] -to [get_ports data_out*]

# 寄存器到寄存器路径
# set_max_delay 10.0 -from [get_registers] -to [get_registers]

# ============================================================================
# 11. 扇出和转换时间约束
# ============================================================================

# 最大扇出约束
set_max_fanout 10 [current_design]

# 最大转换时间约束
set_max_transition 0.3 [current_design]

# 最大电容约束
set_max_capacitance 0.5 [current_design]

# 针对特定路径的约束
# set_max_fanout 5 [get_cells critical_path*]
# set_max_transition 0.2 [get_ports clk]

# ============================================================================
# 12. 时钟偏差约束
# ============================================================================

# 设置时钟偏差（如果时钟树已经存在）
# set_clock_latency -max 1.0 -min 0.5 [get_clocks clk]

# 或设置理想时钟偏差
# set_clock_skew -ideal -max 0.2 -min 0.1 [get_clocks clk]

# ============================================================================
# 13. 面积约束
# ============================================================================

# 最大面积约束（可选）
# set_max_area 10000 [current_design]

# 或设置面积优化目标
# set_max_dynamic_power 100 mW [current_design]
# set_max_leakage_power 10 mW [current_design]

# ============================================================================
# 14. 设计规则约束
# ============================================================================

# 禁止使用的单元（可选）
# set_dont_use [get_lib_cells */DONTUSE_*]

# 避免使用的单元（可选）
# set_dont_touch_network [get_nets preserve_net*]

# 固定网络（不进行优化）
# set_ideal_network [get_nets no_opt_net*]

# ============================================================================
# 15. 保持约束（Hold）
# ============================================================================

# 针对特定路径的hold约束
# set_min_delay 0.5 -from [get_cells regA/Q] -to [get_cells regB/D]

# 防止hold违例的额外约束
# set_data_check -from [get_pins regA/Q] -to [get_pins regB/D] -hold 0.2

# ============================================================================
# 16. 不定态处理
# ============================================================================

# 处理X态传播
# case_analysis false [get_ports test_mode]

# 不定态传播控制
# set_case_analysis 0 [get_ports reset_n]

# ============================================================================
# 17. 环境约束
# ============================================================================

# 工作条件（PVT）
# set_operating_conditions -min_library "fast.lib" -min "fast" \
#   -max_library "slow.lib" -max "slow"

# 或使用典型条件
# set_operating_conditions -typical_library "typical.lib" -typical "typical"

# 连接负载（如果输出端口连接到特定负载）
# set_load 1.0 [get_ports output_port*]

# ============================================================================
# 18. 接口约束
# ============================================================================

# AXI接口时序约束（示例）
# set_input_delay -clock clk -max 2.0 [get_ports axi_*_data*]
# set_input_delay -clock clk -min 0.5 [get_ports axi_*_data*]
# set_output_delay -clock clk -max 3.0 [get_ports axi_*_data*]
# set_output_delay -clock clk -min 1.0 [get_ports axi_*_data*]

# ============================================================================
# 19. 时钟使能约束
# ============================================================================

# 时钟使能信号（如果有）
# set_case_analysis 1 [get_ports clock_enable]
# set_case_analysis 0 [get_ports clock_disable]

# ============================================================================
# 20. 特殊单元约束
# ============================================================================

# 存储器单元（如果有）
# set_dont_touch [get_cells memory_instance*]

# 模拟单元（如果有）
# set_dont_touch [get_cells analog_block*]

# I/O单元（如果有）
# set_dont_touch [get_cells io_cell*]

# ============================================================================
# 注释说明
# ============================================================================
#
# 1. 根据实际设计修改端口名称和延迟值
# 2. 时钟周期和不确定性应根据设计规格和工艺特性调整
# 3. 输入/输出延迟应根据实际接口时序计算
# 4. 驱动单元应根据实际驱动器件选择
# 5. 负载电容应根据实际负载计算
# 6. 虚假路径和多周期路径应谨慎设置
# 7. 约束应覆盖所有设计端口和关键路径
# 8. 定期检查约束是否合理和完整
#
# ============================================================================
