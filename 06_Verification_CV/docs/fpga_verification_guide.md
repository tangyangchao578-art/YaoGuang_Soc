# YaoGuang SoC FPGA验证指南

**文档版本**: v1.0  
**编制日期**: 2026年1月18日  
**编制人**: CV验证团队

---

## 1. 概述

### 1.1 文档目的

本文档为YaoGuang SoC芯片的FPGA原型验证提供完整的技术指南，包括FPGA环境搭建、综合与实现、比特流生成和板级调试等内容。通过本指南，验证工程师能够搭建FPGA原型验证环境并进行系统级验证。

### 1.2 FPGA验证目标

FPGA原型验证的主要目标包括：
- 验证SoC顶层功能正确性
- 验证软硬件协同工作
- 验证启动流程和操作系统启动
- 验证外设接口和驱动程序
- 性能基准测试
- 系统稳定性验证

### 1.3 FPGA平台配置

| 配置项 | 规格 |
|-------|------|
| FPGA器件 | Xilinx VU19P |
| 逻辑单元 | 8.9M |
| 查找表(LUT) | 3.5M |
| 触发器(FF) | 7.0M |
| BRAM | 68Mb |
| DSP Slice | 6840 |
| DDR4 | 16GB (4×4GB) |
| 高速接口 | 100G Ethernet, PCIe Gen4×16 |
| 板卡 | Xilinx VCU118 |

---

## 2. FPGA环境搭建

### 2.1 硬件环境准备

#### 2.1.1 开发板检查

```bash
# 检查板卡连接状态
lsusb | grep -i xilinx
# 预期输出: Bus xxx Device xxx: ID 03fd:005f Xilinx, Inc.

# 检查JTAG连接
ls /dev/ttyUSB*
# 预期输出: /dev/ttyUSB0 (JTAG), /dev/ttyUSB1 (USB-UART)

# 检查电源指示灯
# 确认12V电源指示灯亮起

# 检查FPGA DONE指示灯
# 确认FPGA配置完成指示灯状态
```

#### 2.1.2 连接图

```
┌─────────────────────────────────────────────────────────────┐
│                    FPGA原型验证系统                           │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌─────────────┐      USB      ┌─────────────┐              │
│  │  开发工作站   │◄────────────►│  FPGA开发板  │              │
│  │  (运行Vivado │      JTAG     │  VCU118     │              │
│  │   和测试脚本)│              │             │              │
│  └──────┬──────┘               └──────┬──────┘              │
│         │                             │                     │
│         │    以太网                   │                     │
│         └────────────────────────────►│                     │
│                                       │                     │
│                                ┌──────▼──────┐              │
│                                │  以太网交换机 │              │
│                                └──────┬──────┘              │
│                                       │                     │
│                                ┌──────▼──────┐              │
│                                │  TFTP服务器  │              │
│                                │  (测试镜像)  │              │
│                                └─────────────┘              │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 2.2 软件环境安装

#### 2.2.1 Vivado安装

```bash
# 下载Vivado 2023.2
wget https://www.xilinx.com/bin/public/openDownload?filename=Vivado_2023.2_1015_1007.tar.gz

# 解压安装包
tar -xzf Vivado_2023.2_1015_1007.tar.gz

# 运行安装程序
cd xsetup
./xsetup

# 安装选项
# - Product: Vivado HL Enterprise Edition
# - Devices: Kintex/Virtex UltraScale+
# - Installation Type: Full Installation
```

#### 2.2.2 环境变量设置

```bash
# 创建环境设置脚本
cat > ~/yaoguang_fpga_env.sh << 'EOF'
#!/bin/bash

# Xilinx Vivado
export XILINX_HOME=/opt/xilinx/Vivado/2023.2
export PATH=$XILINX_HOME/bin:$PATH
export PATH=$XILINX_HOME/ids_lite/ISE/bin/lin64:$PATH

# License
export LM_LICENSE_FILE=27000@license-server

# 板卡文件
export BOARD_PART_PATH=$XILINX_HOME/board_files

# 临时目录
export TMPDIR=/tmp/xilinx_$USER
mkdir -p $TMPDIR
EOF

# 加载环境
source ~/yaoguang_fpga_env.sh
```

#### 2.2.3 验证安装

```bash
# 检查Vivado
vivado -version
# 预期输出: Vivado v2023.2 (64-bit)

# 检查License
lmstat -c 27000@license-server -v
# 预期输出: Features: vivado, etc.

# 检查板卡文件
ls $BOARD_PART_PATH/xilinx/vcu118/
# 预期输出: board.xml, presets/, doc/
```

### 2.3 验证工程创建

#### 2.3.1 创建Vivado工程

```tcl
# create_project.tcl
# FPGA原型验证工程创建脚本

# 工程名称和路径
set project_name "yaoguang_soc_fpga"
set project_dir "/home/user/fpga_projects/$project_name"
set part "xcvu9p-flga2104-2-i"

# 创建工程
create_project -name $project_name \
    -dir $project_dir \
    -part $part \
    -force

# 设置工程属性
set_property board_part xilinx.com:vcu118:part0:1.3 [current_project]
set_property default_lib xil_defaultlib [current_project]
set_property simulator_language SystemVerilog [current_project]
set_property source_mgmt_mode None [current_project]

# 添加源文件
add_files -norecurse \
    -fileset sources_1 \
    ../../04_Design_RTL/soc_top/yaoguang_soc_top.sv

add_files -norecurse \
    -fileset sources_1 \
    ../../04_Design_RTL/ip_rtl/*.sv

# 添加约束文件
add_files -norecurse \
    -fileset constrs_1 \
    ./constraints/yaoguang_vcu118.xdc

# 添加IP
add_files -norecurse \
    -fileset sources_1 \
    ./ip/yaoguang_clock.xci
add_files -norecurse \
    -fileset sources_1 \
    ./ip/yaoguang_reset.xci

# 保存工程
save_project_as $project_name $project_dir -force

puts "Project created successfully!"
```

```bash
# 运行工程创建
cd 06_Verification_CV/fpga/scripts
vivado -mode tcl -source create_project.tcl
```

---

## 3. 综合与实现

### 3.1 RTL可综合性检查

#### 3.1.1 可综合性规则检查

```tcl
# synthesis_check.tcl
# RTL可综合性检查

# 读取设计
read_verilog -sv \
    ../../04_Design_RTL/soc_top/yaoguang_soc_top.sv
read_verilog -sv \
    ../../04_Design_RTL/ip_rtl/*.sv

# 设置综合选项
set_param synth.checkpoint.useTree 0
set_param synth.design.resetlevel off

# 运行DRC检查
synth_design -top yaoguang_soc_top \
    -part xcvu9p-flga2104-2-i \
    -no_lc \
    -no_timing_driven

# 检查DRC违例
report_drc -file ./reports/synth_drc.txt

# 查找不可综合的构造
report_undefined -file ./reports/synth_undefined.txt

# 统计资源使用预估
report_utilization -hierarchical \
    -file ./reports/synth_utilization.txt
```

```bash
# 运行可综合性检查
vivado -mode tcl -source synthesis_check.tcl
```

#### 3.1.2 常见不可综合构造

| 构造类型 | 示例 | 替代方案 |
|---------|------|---------|
| initial块 | initial $display("Hello"); | 复位驱动初始化 |
| 延时控制 | #10 clk = ~clk; | 使用时钟分频器 |
| force/release | force clk = 1'b0; | 使用三态门或MUX |
| 异步逻辑 | always @(posedge clk or negedge rst_n) | 使用同步设计 |
| casex/casez | casex(data[3:0]) | 使用完整case |

### 3.2 FPGA综合

#### 3.2.1 综合脚本

```tcl
# synth.tcl
# FPGA综合脚本

# 变量设置
set project_name "yaoguang_soc_fpga"
set project_dir "/home/user/fpga_projects/$project_name"
set top_name "yaoguang_soc_top"
set part "xcvu9p-flga2104-2-i"

# 打开工程
open_project $project_dir/$project_name.xpr

# 设置综合策略
set_strategy "Flow_AreaOptimized_high"

# 运行综合
synth_design -top $top_name \
    -part $part \
    -gated_clock_conversion on \
    -fanout_limit 300 \
    -bufg 32 \
    -keep_equivalent_registers \
    -resource_sharing off

# 优化设计
opt_design

# 报告综合结果
report_timing_summary -file ./reports/synth_timing.txt
report_utilization -hierarchical \
    -file ./reports/synth_utilization.txt
report_drc -file ./reports/synth_drc.txt

# 保存检查点
write_checkpoint -force ./checkpoints/synth/${top_name}_synth.dcp

# 关闭工程
close_project

puts "Synthesis completed!"
```

```bash
# 运行综合
cd 06_Verification_CV/fpga/scripts
make synth PART=xcvu9p-flga2104-2-i
```

#### 3.2.2 综合选项说明

| 选项 | 说明 | 推荐值 |
|------|------|-------|
| -gated_clock_conversion | 门控时钟转换 | on |
| -fanout_limit | 最大扇出限制 | 300 |
| -bufg | 最大BUFG使用数 | 32 |
| -keep_equivalent_registers | 保留等价寄存器 | on |
| -resource_sharing | 资源共享 | off |

### 3.3 布局布线

#### 3.3.1 布局布线脚本

```tcl
# impl.tcl
# 布局布线脚本

# 变量设置
set top_name "yaoguang_soc_top"

# 打开综合检查点
open_checkpoint ./checkpoints/synth/${top_name}_synth.dcp

# 设置实现策略
set_strategy "Performance_Explore"

# 运行布局
place_design

# 优化布局
opt_design

# 运行布线
route_design

# 优化时序
phys_opt_design -directive Explore

# 报告结果
report_timing_summary -file ./reports/impl_timing.txt
report_utilization -hierarchical \
    -file ./reports/impl_utilization.txt
report_power -file ./reports/impl_power.txt
report_drc -file ./reports/impl_drc.txt

# 保存检查点
write_checkpoint -force ./checkpoints/impl/${top_name}_impl.dcp

# 生成比特流
write_bitstream -force ./bitstreams/${top_name}.bit

puts "Implementation completed!"
```

```bash
# 运行布局布线
cd 06_Verification_CV/fpga/scripts
make impl PART=xcvu9p-flga2104-2-i
```

#### 3.3.2 时序约束文件

```tcl
# yaoguang_vcu118.xdc
# 时序约束文件

# 主时钟定义
create_clock -period 8.0 -name clk_sys [get_pins clk_gen_inst/O]
create_clock -period 4.0 -name clk_ddr [get_pins ddr_controller_inst/clk_ref]
create_clock -period 10.0 -name clk_cpu [get_pins cpu_inst/clk]

# 衍生时钟
create_generated_clock -name clk_cpu_div2 \
    -source [get_pins cpu_inst/clk] \
    -divide_by 2 [get_pins clk_div2_reg/Q]

# 输入延迟
set_input_delay -clock clk_sys -max 2.0 [get_ports sys_pins_*]
set_input_delay -clock clk_sys -min 1.0 [get_ports sys_pins_*]

# 输出延迟
set_output_delay -clock clk_sys -max 1.5 [get_ports gpio_pins_*]
set_output_delay -clock clk_sys -min 0.5 [get_ports gpio_pins_*]

# 假路径
set_false_path -from [get_pins reset_sync*/PRE]
set_false_path -from [get_pins async_fifo*/wr_clk] \
                -to [get_pins async_fifo*/rd_clk]

# 多周期路径
set_multicycle_path -from [get_pins axi_master*/M_VALID] \
                    -to [get_pins axi_slave*/S_READY] \
                    -setup 2
set_multicycle_path -from [get_pins axi_master*/M_VALID] \
                    -to [get_pins axi_slave*/S_READY] \
                    -hold 1

# 时钟组
set_clock_groups -asynchronous \
    -group clk_sys \
    -group clk_ddr \
    -group clk_cpu
```

---

## 4. 比特流生成

### 4.1 比特流配置

#### 4.1.1 比特流生成脚本

```tcl
# bitstream.tcl
# 比特流生成脚本

# 变量设置
set top_name "yaoguang_soc_top"

# 打开实现检查点
open_checkpoint ./checkpoints/impl/${top_name}_impl.dcp

# 配置比特流选项
set_property BITSTREAM.GENERAL.COMPRESSED TRUE [current_design]
set_property BITSTREAM.CONFIG.UNUSEDPIN PULLDOWN [current_design]
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH 4 [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE 66 [current_design]

# 生成比特流
write_bitstream -force \
    -bin_file \
    ./bitstreams/${top_name}.bit

# 生成MCS文件(用于Flash编程)
write_cfgmem -format mcs -size 128 \
    -interface SPIx4 \
    -loadbit {up 0x0 ./bitstreams/${top_name}.bit} \
    -file ./bitstreams/${top_name}.mcs

# 报告比特流信息
report_bitstream -file ./reports/bitstream_info.txt

puts "Bitstream generation completed!"
```

```bash
# 生成比特流
cd 06_Verification_CV/fpga/scripts
make bitstream PART=xcvu9p-flga2104-2-i
```

#### 4.1.2 比特流文件

| 文件类型 | 文件名 | 用途 |
|---------|--------|------|
| 比特流 | yaoguang_soc_top.bit | JTAG直接下载 |
| MCS | yaoguang_soc_top.mcs | Flash编程 |
| BIN | yaoguang_soc_top.bin | 远程更新 |
| 报告 | bitstream_info.txt | 比特流统计信息 |

### 4.2 比特流下载

#### 4.2.1 JTAG下载

```bash
# 使用Vivado下载比特流
cd 06_Verification_CV/fpga/scripts

# 打开硬件管理器
vivado -mode gui &

# 在Hardware窗口中连接目标板
# 选择Hardware Device → Auto Connect

# 下载比特流
open_hw
connect_hw_server -url localhost:3121
open_hw_target - hw_server localhost:3121 -xvc_tcf
current_hw_target

# 下载比特流
set_property PROGRAM.FILE {./bitstreams/yaoguang_soc_top.bit} [current_hw_device]
program_hw_devices [current_hw_device]
refresh_hw_device [current_hw_device]
```

```bash
# 命令行下载
vivado -mode batch -source download_bitstream.tcl
```

#### 4.2.2 Flash编程

```tcl
# flash_program.tcl
# Flash编程脚本

# 连接硬件
open_hw
connect_hw_server -url localhost:3121
open_hw_target - hw_server localhost:3121 -xvc_tcf

# 擦除Flash
set_property PROGRAM.ERASE true [current_hw_device]
program_hw_devices [current_hw_device]
refresh_hw_device [current_hw_device]

# 编程Flash
set_property PROGRAM.FILE {./bitstreams/yaoguang_soc_top.mcs} [current_hw_device]
set_property PROGRAM.ERASE true [current_hw_device]
set_property PROGRAM.CFG_PROGRAM true [current_hw_device]
set_property PROGRAM.VERIFY true [current_hw_device]
program_hw_devices [current_hw_device]
refresh_hw_device [current_hw_device]

# 验证
verify_hw_devices [current_hw_device]

puts "Flash programming completed!"
```

---

## 5. 板级调试

### 5.1 调试环境搭建

#### 5.1.1 串口连接

```bash
# 安装串口工具
sudo apt-get install minicom screen

# 连接串口
sudo minicom -D /dev/ttyUSB1 -b 115200

# 或使用screen
sudo screen /dev/ttyUSB1 115200

# 串口参数
# 波特率: 115200
# 数据位: 8
# 停止位: 1
# 校验: None
# 流控: None
```

#### 5.1.2 以太网连接

```bash
# 配置FPGA板卡IP地址
# 通过U-Boot或Linux配置
setenv ipaddr 192.168.1.100
setenv serverip 192.168.1.200
saveenv

# 测试网络连接
ping 192.168.1.200

# 配置TFTP服务器
sudo systemctl start tftp-hpa
sudo cp u-boot.bin /var/lib/tftpboot/
```

### 5.2 在线调试

#### 5.2.1 ILA调试核配置

```tcl
# ila_debug.tcl
# ILA调试核配置脚本

# 创建ILA调试核
create_debug_core u_ila_0 ila

# 设置ILA参数
set_property C_DATA_DEPTH 32768 [get_debug_cores u_ila_0]
set_property C_TRIG_IN_COUNT 1 [get_debug_cores u_ila_0]
set_property C_TRIG_OUT_COUNT 1 [get_debug_cores u_ila_0]
set_property C_INPUT_PIPE_STAGES 0 [get_debug_cores u_ila_0]
set_property C_OUTPUT_PIPE_STAGES 0 [get_debug_cores u_ila_0]

# 连接时钟
connect_debug_port u_ila_0/clk [get_nets clk_sys]

# 添加触发信号
create_debug_port u_ila_0 probe
set_property PROBE_WIDTH 32 [get_debug_ports u_ila_0/probe0]
connect_debug_port u_ila_0/probe0 [get_nets axi_awvalid]
set_property PROBE_WIDTH 32 [get_debug_ports u_ila_0/probe1]
connect_debug_port u_ila_0/probe1 [get_nets axi_awready]
set_property PROBE_WIDTH 64 [get_debug_ports u_ila_0/probe2]
connect_debug_port u_ila_0/probe2 [get_nets axi_wdata]

# 保存约束
save_constraints -force ./constraints/debug.xdc

# 重新实现
implement_design
write_bitstream -force ./bitstreams/yaoguang_soc_top_debug.bit
```

#### 5.2.2 触发条件设置

```tcl
# 简单触发 - 单一条件触发
set_property TriggerSetup {axi_awvalid == 1'b1} [get_hw_ilas -of_objects [get_hw_devices -of_objects [current_hw_target]]]

# 组合触发 - 多条件与
set_property TriggerSetup {axi_awvalid == 1'b1 && axi_wdata == 64'hDEADBEEF} [get_hw_ilas -of_objects [get_hw_devices -of_objects [current_hw_target]]]

# 序列触发 - 事件序列
set_property TriggerSequence {axi_awvalid[=]1 && axi_awready[=]1 => axi_wvalid[=]1} [get_hw_ilas -of_objects [get_hw_devices -of_objects [current_hw_target]]]

# 触发位置设置
set_property TriggerPosition 16384 [get_hw_ilas -of_objects [get_hw_devices -of_objects [current_hw_target]]]

# 运行触发
run_hw_ila -trigger [get_hw_ilas -of_objects [get_hw_devices -of_objects [current_hw_target]]]
```

### 5.3 信号分析

#### 5.3.1 波形查看

```tcl
# 在Vivado Hardware Manager中
# 1. 选择ILA核
# 2. 点击"Waveform"窗口
# 3. 添加要查看的信号
# 4. 设置触发条件
# 5. 运行触发
# 6. 分析波形
```

#### 5.3.2 信号完整性分析

```bash
# 使用ChipScope分析
# 1. 打开ChipScope Analyzer
# 2. 连接目标板
# 3. 导入CDC文件
# 4. 设置触发条件
# 5. 捕获和分析波形
```

### 5.4 常见问题处理

#### 5.4.1 FPGA配置问题

| 问题 | 可能原因 | 解决方法 |
|------|---------|---------|
| DONE灯不亮 | 比特流错误 | 重新生成比特流 |
| JTAG连接失败 | 驱动问题 | 重新安装驱动 |
| 配置失败 | Flash损坏 | 擦除后重新编程 |
| 时钟不稳定 | PCB问题 | 检查时钟电路 |

#### 5.4.2 运行时问题

| 问题 | 可能原因 | 解决方法 |
|------|---------|---------|
| 系统不启动 | DDR未初始化 | 检查DDR时序约束 |
| 随机错误 | 时序违例 | 降低频率或优化时序 |
| 发热严重 | 设计过大 | 优化设计资源使用 |
| 内存错误 | 内存控制器问题 | 检查DDR初始化序列 |

---

## 6. 验证测试

### 6.1 基本功能测试

```bash
# FPGA启动测试
cd 06_Verification_CV/fpga/scripts
make fpga_download BITSTREAM=../bitstreams/yaoguang_soc_top.bit

# 打开串口
make open_uart PORT=/dev/ttyUSB1 BAUD=115200

# 预期输出
# U-Boot 2023.10-rc2
# Model: YaoGuang SoC FPGA Prototype
# DRAM:  4 GiB
# MMC:   sdhci@ff160000: 0
# In:    serial@ff010000
# Out:   serial@ff010000
# Err:   serial@ff010000
# Net:   eth0: ethernet@ff0e0000
# Hit any key to stop autoboot:  0
# =>
```

### 6.2 自动化测试

```bash
# 运行所有FPGA测试
make fpga_test_all

# 运行单次测试
make fpga_test TEST=boot_test
make fpga_test TEST=ddr_test
make fpga_test TEST=uart_test
make fpga_test TEST=network_test

# 压力测试
make fpga_stress_test HOURS=72
```

### 6.3 测试报告

```bash
# 生成测试报告
cd 06_Verification_CV/fpga
./scripts/generate_fpga_report.py

# 报告位置
# 06_Verification_CV/fpga/reports/fpga_test_report.html
# 06_Verification_CV/fpga/reports/fpga_test_report.txt
```

---

**文档结束**
