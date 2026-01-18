# YaoGuang SoC Emulation验证指南

**文档版本**: v1.0  
**编制日期**: 2026年1月18日  
**编制人**: CV验证团队

---

## 1. 概述

### 1.1 文档目的

本文档为YaoGuang SoC芯片的硬件加速仿真(Emulation)验证提供完整的技术指南，包括Emulation环境配置、RTL编译、性能测试和结果分析等内容。通过本指南，验证工程师能够搭建高效的Emulation验证环境并进行大规模系统级验证。

### 1.2 Emulation平台概述

| 配置项 | Palladium Z1 | 描述 |
|-------|-------------|------|
| 门数 | 16B门 | 相当于16亿门 |
| 触发器 | 8.8M | 触发器数量 |
| BRAM | 144Mb | 块RAM容量 |
| 编译时间 | ~2小时 | 完整编译时间 |
| 运行速度 | ~1-2MHz | 仿真速度 |
| 主机接口 | PCIe Gen4×16 | 主机通信接口 |
| 内存带宽 | 8GB/s | 主机-DUT带宽 |

### 1.3 Emulation验证优势

| 特性 | RTL仿真 | Emulation | 优势 |
|------|---------|----------|------|
| 仿真速度 | ~100Hz | ~1MHz | 10,000x加速 |
| 测试规模 | 1000条指令 | 10亿条指令 | 1,000,000x |
| 回归时间 | 2天 | 2小时 | 24x加速 |
| 软硬件协同 | 受限 | 完全支持 | 完整验证 |
| 调试能力 | 完整 | 有限 | 互补 |

---

## 2. Emulation环境配置

### 2.1 硬件环境准备

#### 2.1.1 Palladium Z1机柜配置

```
┌─────────────────────────────────────────────────────────────┐
│                   Palladium Z1机柜                           │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌─────────────────────────────────────────────────────┐   │
│  │  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐│   │
│  │  │ FPGA    │  │ FPGA    │  │ FPGA    │  │ FPGA    ││   │
│  │  │ Tile 0  │  │ Tile 1  │  │ Tile 2  │  │ Tile 3  ││   │
│  │  │ 4B门    │  │ 4B门    │  │ 4B门    │  │ 4B门    ││  emu
│  │  └────┬────┘  └────┬────┘  └────┬────┘  └────┬────┘│   │
│  │       │            │            │            │     │   │
│  │       └────────────┴─────┬──────┴────────────┘     │   │
│  │                          │                          │   │
│  │                   ┌──────▼──────┐                  │   │
│  │                   │  NoC互连     │                  │   │
│  │                   │  1.2Tbps    │                  │   │
│  │                   └──────┬──────┘                  │   │
│  │                          │                          │   │
│  │  ┌───────────────────────┼───────────────────────┐  │   │
│  │  │                       │                       │  │   │
│  │  │              ┌────────▼────────┐              │  │   │
│  │  │              │  主机接口卡      │              │  │   │
│  │  │              │  PCIe Gen4×16   │              │  │   │
│  │  │              └────────┬────────┘              │  │   │
│  │  │                       │                       │  │   │
│  │  │              ┌────────▼────────┐              │  │   │
│  │  │              │  内存控制器      │              │  │   │
│  │  │              │  16GB DDR4      │              │  │   │
│  │  │              └─────────────────┘              │  │   │
│  │  └───────────────────────────────────────────────┘  │   │
│  └─────────────────────────────────────────────────────┘   │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

#### 2.1.2 网络配置

```bash
# 配置Palladium管理网络
# 连接到管理网络交换机
# IP地址: 192.168.10.100
# 子网掩码: 255.255.255.0
# 网关: 192.168.10.1

# 测试连接
ping 192.168.10.100

# 配置主机网络
sudo ip addr add 192.168.10.200/24 dev eth0
sudo ip link set eth0 up
```

### 2.2 软件环境安装

#### 2.2.1 Palladium软件安装

```bash
# 安装Palladium软件
cd /opt/cadence/palladium_23.1
./setup.pl

# 环境变量设置
cat > ~/yaoguang_emu_env.sh << 'EOF'
#!/bin/bash

# Palladium
export EMU_HOME=/opt/cadence/palladium_23.1
export PATH=$EMU_HOME/bin:$PATH
export LD_LIBRARY_PATH=$EMU_HOME/lib:$LD_LIBRARY_PATH

# License
export LM_LICENSE_FILE=27000@license-server

# 临时目录
export TMPDIR=/tmp/palladium_$USER
mkdir -p $TMPDIR
EOF

source ~/yaoguang_emu_env.sh
```

#### 2.2.2 验证安装

```bash
# 检查Palladium
emu -version
# 预期输出: Palladium Emulation System 23.1

# 检查License
lmstat -c 27000@license-server -v | grep palladium

# 检查硬件连接
emu -status
# 预期输出: Palladium Z1 connected and ready
```

### 2.3 Emulation工程配置

#### 2.3.1 编译配置文件

```tcl
# emu_compile.tcl
# Emulation编译配置文件

# 设置编译选项
set_option emucompiler xcelium

# 时钟配置
set_option clock -clk clk_sys -period 8.0
set_option clock -clk clk_ddr -period 4.0
set_option clock -clk clk_cpu -period 2.0

# 异步时钟处理
set_option disableclockgating true
set_option asynchmode on

# 内存映射配置
# DDR内存模型
set_option memory -name ddr_model \
    -type 4GB \
    -interface axi4 \
    -latency 10

# SRAM内存模型
set_option memory -name sram_model \
    -type 1MB \
    -interface apb \
    -latency 1

# 编译优化
set_option emuoptimization -frequency 2MHz
set_option emuoptimization -pipeline on
set_option emuoptimization -resource_sharing on

# 调试配置
set_option debug -all
set_option visibility -full

# 添加源文件
read_verilog -sv \
    ../../04_Design_RTL/soc_top/yaoguang_soc_top.sv

read_verilog -sv \
    ../../04_Design_RTL/ip_rtl/*.sv

# 读取约束
read_xdc ./constraints/yaoguang_emu.xdc

# 设置顶层模块
set_option top yaoguang_soc_top

# 开始编译
compile
```

```tcl
# yaoguang_emu.xdc
# Emulation时序约束

# 主时钟定义
create_clock -period 8.0 -name clk_sys
create_clock -period 4.0 -name clk_ddr

# 异步时钟域
set_clock_groups -asynchronous \
    -group clk_sys \
    -group clk_ddr \
    -group clk_cpu

# Emulation特定约束
set_false_path -from [get_pins */rst_n_sync*]
set_max_delay -from [get_clocks clk_sys] -to [get_clocks clk_ddr] 10.0
```

---

## 3. RTL编译

### 3.1 编译流程

```bash
# 进入编译目录
cd 06_Verification_CV/emulation/scripts

# 开始编译
make compile TARGET=emu

# 编译进度查看
tail -f compile.log

# 预计编译时间: 2-4小时
```

```bash
# 编译流程说明
┌────────────────────────────────────────────────────────────┐
│  Emulation编译流程                                          │
├────────────────────────────────────────────────────────────┤
│                                                            │
│  RTL分析 ──► 时钟分区 ──► 映射到FPGA ──► 编译              │
│      │           │             │            │              │
│      ▼           ▼             ▼            ▼              │
│  语法检查   时钟域划分   资源映射     门级网表              │
│                                                            │
│  ┌───────────────────────────────────────────────────┐    │
│  │                    编译步骤                        │    │
│  │  1. 解析RTL代码 (30分钟)                          │    │
│  │  2. 时钟域分析 (15分钟)                           │    │
│  │  3. 时序约束处理 (10分钟)                         │    │
│  │  4. FPGA资源映射 (1小时)                          │    │
│  │  5. 综合优化 (30分钟)                             │    │
│  │  6. 位流生成 (30分钟)                             │    │
│  └───────────────────────────────────────────────────┘    │
│                                                            │
└────────────────────────────────────────────────────────────┘
```

### 3.2 编译选项

| 选项 | 说明 | 推荐值 |
|------|------|-------|
| -freq | 仿真目标频率 | 2MHz |
| -pipeline | 流水线优化 | on |
| -opt | 资源优化 | balanced |
| -debug | 调试信息 | full |
| -partitions | 时钟分区数 | auto |

### 3.3 编译问题处理

```bash
# 查看编译日志
cat compile.log | grep -i error

# 常见编译错误
# 1. 语法错误 - 检查RTL代码
# 2. 时钟冲突 - 调整时钟约束
# 3. 资源不足 - 优化设计或增加分区
# 4. 内存不足 - 增加系统内存

# 增量编译
make compile INCREMENTAL=1
```

---

## 4. 性能测试

### 4.1 性能测试配置

#### 4.1.1 性能测试用例

| 测试项目 | 测试内容 | 预期性能 |
|---------|---------|---------|
| DDR带宽测试 | 连续256MB读写 | ≥20GB/s |
| NPU性能测试 | 矩阵运算吞吐量 | ≥3TOPS |
| 启动时间测试 | 上电到Linux启动 | ≤500ms |
| 中断延迟测试 | 中断响应时间 | ≤500ns |
| DMA传输测试 | 大块数据传输速率 | ≥5GB/s |

#### 4.1.2 性能测试脚本

```c
// perf_test.c
// Emulation性能测试用例

#include <stdio.h>
#include <stdlib.h>
#include <time.h>

// DDR带宽测试
void ddr_bandwidth_test(void) {
    uint64_t *src = (uint64_t *)0x80000000;
    uint64_t *dst = (uint64_t *)0x90000000;
    size_t size = 256 * 1024 * 1024; // 256MB
    double time_sec;
    
    // 写测试
    uint64_t start = read_cycle_counter();
    for (size_t i = 0; i < size / 8; i++) {
        src[i] = i;
    }
    uint64_t end = read_cycle_counter();
    time_sec = (end - start) / 1000000000.0;
    double write_bandwidth = (size / time_sec) / 1e9;
    
    // 读测试
    start = read_cycle_counter();
    uint64_t sum = 0;
    for (size_t i = 0; i < size / 8; i++) {
        sum += dst[i];
    }
    end = read_cycle_counter();
    time_sec = (end - start) / 1000000000.0;
    double read_bandwidth = (size / time_sec) / 1e9;
    
    printf("DDR Bandwidth Test Results:\n");
    printf("  Write: %.2f GB/s\n", write_bandwidth);
    printf("  Read:  %.2f GB/s\n", read_bandwidth);
    printf("  Total: %.2f GB/s\n", write_bandwidth + read_bandwidth);
}

// NPU性能测试
void npu_performance_test(void) {
    // 配置NPU进行矩阵乘法
    matrix_config_t config;
    config.rows = 1024;
    config.cols = 1024;
    config.ops = MATRIX_MULTIPLY;
    
    uint64_t start = read_cycle_counter();
    npu_execute(&config);
    npu_wait_done();
    uint64_t end = read_cycle_counter();
    
    double time_sec = (end - start) / 1000000000.0;
    double ops = 2.0 * 1024 * 1024 * 1024; // 2*N^3 for matrix multiply
    double performance = ops / time_sec / 1e12;
    
    printf("NPU Performance Test Results:\n");
    printf("  Time: %.3f seconds\n", time_sec);
    printf("  Performance: %.2f TOPS\n", performance);
}
```

### 4.2 性能测试执行

```bash
# 运行性能测试
cd 06_Verification_CV/emulation/scripts
make run_perf_test TARGET=emu

# 运行所有测试
make run_all TARGET=emu

# 运行回归测试
make run_regression TARGET=emu
```

### 4.3 性能结果分析

```bash
# 查看性能测试结果
cat ../runlogs/perf_test/output.log

# 预期输出示例
Performance Test Results
========================

DDR Bandwidth Test:
  Write: 28.5 GB/s
  Read:  28.3 GB/s
  Total: 56.8 GB/s
  Status: PASS

NPU Performance Test:
  Time: 0.245 seconds
  Performance: 4.2 TOPS
  Status: PASS

Boot Time Test:
  Total Boot Time: 156 ms
  Status: PASS

Interrupt Latency Test:
  Average Latency: 320 ns
  Max Latency: 450 ns
  Status: PASS
```

---

## 5. 结果分析

### 5.1 仿真日志分析

```bash
# 查看仿真日志
cd 06_Verification_CV/emulation/runlogs
cat ddr_test/output.log

# 日志格式
[TIMESTAMP] [LEVEL] [MODULE] Message
[2026-01-18 10:30:15.123] [INFO] [DDR] Starting DDR initialization
[2026-01-18 10:30:15.456] [INFO] [DDR] DDR PLL locked
[2026-01-18 10:30:15.789] [INFO] [DDR] DDR initialization complete
[2026-01-18 10:30:16.012] [PASS] [DDR] DDR bandwidth test passed
```

### 5.2 覆盖率分析

```bash
# 生成覆盖率报告
make coverage TARGET=emu

# 查看覆盖率报告
firefox ../coverage_reports/html/index.html

# 命令行查看覆盖率
cat ../coverage_reports/summary/coverage_summary.txt
```

### 5.3 波形分析

```bash
# 导出波形
make dump_wave TEST=ddr_test TARGET=emu

# 查看波形
verdi -ssrc/wave.fsdb &
```

### 5.4 性能对比分析

| 测试项目 | 仿真结果 | Emulation结果 | 目标值 | 状态 |
|---------|---------|--------------|--------|------|
| DDR带宽 | 28.5 GB/s | 28.2 GB/s | ≥25GB/s | ✓ 达成 |
| NPU性能 | 4.2 TOPS | 4.1 TOPS | ≥4TOPS | ✓ 达成 |
| 启动时间 | 156ms | 158ms | ≤200ms | ✓ 达成 |
| 中断延迟 | 320ns | 325ns | ≤500ns | ✓ 达成 |

---

## 6. 软硬件协同验证

### 6.1 软件环境搭建

```bash
# 配置交叉编译工具链
export CROSS_COMPILE=aarch64-linux-gnu-
export TOOLCHAIN_PATH=/opt/toolchain/aarch64-2023.09

# 编译测试程序
cd 06_Verification_CV/c_tests
make clean
make ARCH=arm64

# 生成测试固件
python3 scripts/gen_firmware.py \
    --input c_tests/ \
    --output ../emulation/firmware/ \
    --format elf
```

### 6.2 协同验证流程

```
┌─────────────────────────────────────────────────────────────────┐
│              软硬件协同验证流程                                   │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  1. 软件开发                                                      │
│     ┌─────────┐    ┌─────────┐    ┌─────────┐                 │
│     │ 编写C   │───►│ 编译    │───►│ 生成    │                 │
│     │ 测试程序 │    │ 固件    │    │ ELF    │                 │
│     └─────────┘    └─────────┘    └─────────┘                 │
│          │                              │                       │
│          ▼                              ▼                       │
│  2. Emulation加载                                                │
│     ┌─────────────────────────────────────────┐                │
│     │         加载固件到Emulation内存           │                │
│     └─────────────────────────────────────────┘                │
│                           │                                     │
│                           ▼                                     │
│  3. 协同仿真                                                      │
│     ┌─────────────────────────────────────────┐                │
│     │  ┌─────────┐    ┌─────────┐            │                │
│     │  │ 软件执行 │◄──►│ 硬件执行 │            │                │
│     │  └─────────┘    └─────────┘            │                │
│     └─────────────────────────────────────────┘                │
│                           │                                     │
│                           ▼                                     │
│  4. 结果验证                                                      │
│     ┌─────────────────────────────────────────┐                │
│     │         检查输出、覆盖率、错误日志         │                │
│     └─────────────────────────────────────────┘                │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 6.3 协同验证测试

```bash
# 运行协同验证测试
cd 06_Verification_CV/emulation/scripts
make run_sw_test TEST=boot_test TARGET=emu
make run_sw_test TEST=linux_test TARGET=emu
make run_sw_test TEST=driver_test TARGET=emu
```

---

## 7. 回归测试

### 7.1 回归配置

```yaml
# regression.yaml
# 回归测试配置

regression:
  name: yaoguang_cv_regression
  target: emulation
  
  suites:
    boot_tests:
      - test_rom_boot
      - test_uboot
      - test_linux_boot
    
    ddr_tests:
      - test_ddr_basic_rw
      - test_ddr_bandwidth
      - test_ddr_stress
    
    peripheral_tests:
      - test_uart
      - test_spi
      - test_i2c
      - test_can
    
    interrupt_tests:
      - test_interrupt
      - test_nested_interrupt
      - test_interrupt_latency
    
    safety_tests:
      - test_ecc
      - test_lockstep
      - test_watchdog
  
  settings:
    parallel: 4
    timeout: 300
    coverage: true
    restart_on_fail: false
```

### 7.2 运行回归

```bash
# 运行完整回归
cd 06_Verification_CV/emulation
python3 scripts/run_regression.py --config regression.yaml --full

# 运行冒烟回归
python3 scripts/run_regression.py --config regression.yaml --smoke

# 运行特定套件
python3 scripts/run_regression.py --config regression.yaml --suite boot_tests

# 运行并生成报告
python3 scripts/run_regression.py --config regression.yaml \
    --suite all \
    --report html \
    --output reports/
```

### 7.3 回归报告

```bash
# 查看回归报告
firefox ../reports/regression_latest/index.html

# 回归报告内容
==============================
Emulation Regression Report
==============================
Date: 2026-01-18
Duration: 4 hours 32 minutes
------------------------------
Total Tests:    753
Passed:         747
Failed:         6
Pass Rate:      99.2%
------------------------------
Coverage:
  Line:     97.2%
  Branch:   93.5%
  Func:     95.9%
------------------------------
Failed Tests:
  - CV-DDR-048: tRCD timing boundary (known issue)
  - CV-PERIPH-063: SPI clock polarity (fixed)
```

---

## 8. 常见问题处理

### 8.1 编译问题

| 问题 | 原因 | 解决方法 |
|------|------|---------|
| 编译超时 | 设计太大 | 增加分区，优化设计 |
| 内存不足 | 资源使用过高 | 减少调试信息 |
| 时钟错误 | 时钟约束冲突 | 检查时钟定义 |
| 语法错误 | RTL代码问题 | 修复RTL代码 |

### 8.2 运行时问题

| 问题 | 原因 | 解决方法 |
|------|------|---------|
| 仿真挂起 | 死循环 | 设置超时，添加打印 |
| 性能下降 | 调试模式 | 关闭不必要的调试 |
| 内存溢出 | 测试用例问题 | 检查内存访问 |
| 连接失败 | 网络问题 | 检查网络配置 |

### 8.3 调试技巧

```bash
# 1. 使用有限仿真
make run TEST=test_name MAX_CYCLES=1000000

# 2. 添加调试打印
#define DEBUG_PRINT printf

# 3. 使用检查点
make checkpoint TEST=test_name

# 4. 增量调试
make debug TEST=test_name
```

---

**文档结束**
