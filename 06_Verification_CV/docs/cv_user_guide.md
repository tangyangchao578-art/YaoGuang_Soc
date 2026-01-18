# YaoGuang SoC CV用户指南

**文档版本**: v1.0  
**编制日期**: 2026年1月18日  
**编制人**: CV验证团队

---

## 1. 概述

### 1.1 文档目的

本文档旨在为YaoGuang SoC芯片的CV（系统级）验证用户提供完整的操作指南，包括验证环境搭建、测试编译运行、结果查看以及常见问题处理等内容。通过本指南，用户能够快速上手并完成CV验证相关工作。

### 1.2 适用范围

本指南适用于以下人员：
- 芯片验证工程师
- 软件开发工程师
- 硬件调试工程师
- 项目管理人员
- 质量保证人员

### 1.3 文档结构

| 章节 | 内容 |
|------|------|
| 第1章 | 概述 |
| 第2章 | 环境搭建 |
| 第3章 | 编译命令 |
| 第4章 | 运行测试 |
| 第5章 | 查看结果 |
| 第6章 | 常见问题 |

---

## 2. 环境搭建

### 2.1 系统要求

#### 2.1.1 硬件要求

| 组件 | 最低配置 | 推荐配置 |
|------|---------|---------|
| CPU | Intel i7 / AMD Ryzen 7 | Intel i9 / AMD Ryzen 9 |
| 内存 | 32GB | 64GB或更高 |
| 硬盘 | 100GB可用空间 | 500GB NVMe SSD |
| 显卡 | 支持OpenGL 3.3 | NVIDIA RTX系列 |
| 网络 | 千兆以太网 | 万兆以太网 |

#### 2.1.2 操作系统要求

| 操作系统 | 版本 | 支持状态 |
|---------|------|---------|
| Ubuntu | 20.04 LTS / 22.04 LTS | ✓ 完全支持 |
| CentOS | 7 / 8 | ✓ 完全支持 |
| Red Hat Enterprise | 8 / 9 | ✓ 完全支持 |
| Windows | 10 / 11 (WSL2) | ⚠ 部分支持 |

### 2.2 必需软件安装

#### 2.2.1 EDA工具安装

```bash
# 设置环境变量
export SYNOPSYS_HOME=/opt/synopsys/vcs-mx-2023.09
export CADENCE_HOME=/opt/cadence/xcelium-23.1
export XILINX_HOME=/opt/xilinx/Vivado/2023.2

# 添加到PATH
export PATH=$SYNOPSYS_HOME/bin:$PATH
export PATH=$CADENCE_HOME/bin:$PATH
export PATH=$XILINX_HOME/bin:$PATH

# 设置License
export LM_LICENSE_FILE=27000@license-server
```

#### 2.2.2 Python环境配置

```bash
# 创建Python虚拟环境
python3 -m venv cv_venv
source cv_venv/bin/activate

# 安装必需Python包
pip install --upgrade pip
pip install pyyaml json5 matplotlib pandas numpy
pip install jinja2 tabulate colorlog

# 安装验证专用包
pip install -e git+https://gitlab.example.com/cv/cv-utils.git#egg=cv_utils
```

#### 2.2.3 验证环境设置

```bash
# 克隆验证仓库
git clone https://gitlab.example.com/yaoguang/cv-verification.git
cd cv-verification

# 初始化子模块
git submodule update --init --recursive

# 设置环境变量
source setup/env.sh

# 验证环境
cv_env_check
```

### 2.3 目录结构

```
06_Verification_CV/
├── c_tests/                    # C语言测试用例
│   ├── boot/                   # Boot相关测试
│   ├── ddr/                    # DDR相关测试
│   ├── peripheral/             # 外设相关测试
│   ├── interrupt/              # 中断相关测试
│   ├── dma/                    # DMA相关测试
│   └── safety/                 # 安全相关测试
├── emulation/                  # Emulation相关
│   ├── scripts/                # 编译和运行脚本
│   ├── configs/                # 配置文件
│   └── runlogs/                # 运行日志
├── fpga/                       # FPGA原型相关
│   ├── scripts/                # 综合和实现脚本
│   ├── bitstreams/             # 比特流文件
│   └── testbench/              # FPGA测试平台
├── docs/                       # 文档
│   ├── cv_user_guide.md        # 本用户指南
│   ├── cv_testplan_detail.md   # 测试点详细说明
│   ├── fpga_verification_guide.md  # FPGA验证指南
│   └── emulation_guide.md      # Emulation指南
├── regression/                 # 回归测试
│   ├── testlists/              # 测试列表
│   ├── scripts/                # 回归脚本
│   └── reports/                # 回归报告
├── coverage_reports/           # 覆盖率报告
│   ├── html/                   # HTML格式报告
│   ├── data/                   # 原始覆盖率数据
│   └── summary/                # 汇总报告
├── cv_verification_report.md   # 验证总结报告
└── cv_progress_tracker.md      # 进度跟踪
```

### 2.4 环境验证

```bash
# 运行环境检查脚本
cd 06_Verification_CV
./scripts/check_env.sh

# 预期输出
[INFO] Checking Python version... 3.11.0 ✓
[INFO] Checking EDA tools...
[VCS] vcs-mx-2023.09 ✓
[Xcelium] 23.1 ✓
[Vivado] 2023.2 ✓
[INFO] Checking required tools...
[Git] 2.40.0 ✓
[Make] 4.3 ✓
[Python] 3.11.0 ✓
[INFO] Environment check passed!
```

---

## 3. 编译命令

### 3.1 RTL编译

#### 3.1.1 VCS RTL编译

```bash
# 进入编译目录
cd 06_Verification_CV/emulation/scripts

# 编译整个SoC
make compile TARGET=sim PLATFORM=vcs

# 编译命令详解
# TARGET=sim      - 仿真目标
# PLATFORM=vcs    - 使用VCS仿真器
# TOP=yaoguang_soc_top  - 顶层模块（默认）
# DEBUG=1         - 启用调试信息
# COVERAGE=1      - 启用覆盖率收集

# 只编译特定模块
compile_module() {
    local module=$1
    vlogan -sverilog \
        -f ../filelist/yaoguang.f \
        -work yaoguang_lib \
        +incdir+../rtl/include \
        ../rtl/${module}/top.sv
}
```

#### 3.1.2 Xcelium RTL编译

```bash
# 使用Xcelium编译
make compile TARGET=sim PLATFORM=xcelium

# Xcelium特定选项
# -parasanity     - 启用并行编译
# -genpurge       - 生成清除脚本
# -licqueue      - 等待License可用
```

#### 3.1.3 编译选项说明

| 选项 | 说明 | 示例 |
|------|------|------|
| -sverilog | SystemVerilog支持 | 默认启用 |
| -lca | 低成本版本 | 部分工具需要 |
| -full64 | 64位编译 | 默认64位 |
| +v2k | Verilog-2001兼容 | 默认启用 |
| -debug | 启用调试符号 | 调试时使用 |
| +define+VAR | 定义宏 | +define+SIMULATION |
| +incdir+PATH | Include目录 | +incdir+../rtl/include |

### 3.2 C测试用例编译

#### 3.2.1 交叉编译工具链

```bash
# 设置工具链路径
export CROSS_COMPILE=aarch64-linux-gnu-
export TOOLCHAIN_PATH=/opt/toolchain/aarch64-2023.09

# 验证工具链
${CROSS_COMPILE}gcc --version
# aarch64-linux-gnu-gcc (GCC) 12.2.0

# 编译测试用例
cd 06_Verification_CV/c_tests/boot
make clean
make ARCH=arm64 CROSS_COMPILE=${CROSS_COMPILE}

# 生成测试固件
firmware_builder.py --input test_rom.c \
    --output ../emulation/firmware/rom.bin \
    --format elf
```

#### 3.2.2 编译测试用例

```bash
# 编译单个测试
cd 06_Verification_CV/c_tests/ddr
make test_ddr_basic.c ARCH=arm64

# 批量编译所有测试
cd 06_Verification_CV/c_tests
make all ARCH=arm64

# 编译脚本示例
compile_tests.sh:
```bash
#!/bin/bash

TEST_DIRS="boot ddr peripheral interrupt dma safety"

for dir in $TEST_DIRS; do
    echo "Compiling tests in $dir..."
    cd $dir
    make clean
    make ARCH=arm64 -j$(nproc)
    cd ..
done

echo "All tests compiled successfully!"
```

### 3.3 FPGA综合

#### 3.3.1 Vivado综合

```bash
# 进入FPGA脚本目录
cd 06_Verification_CV/fpga/scripts

# 综合整个设计
make synth PLATFORM=vu19p

# 综合选项
# PART=xcvu19p-flva2104-2-i   - 目标器件
# TIMING=1                     - 时序驱动综合
# RESOURCE_OPT=1               - 资源优化
# POWER_OPT=1                  - 功耗优化

# 增量综合（修改后）
make synth INCREMENTAL=1

# 查看综合报告
cat ../reports/synthesis/yaoguang_synth.rpt
```

#### 3.3.2 综合脚本示例

```tcl
# synthesis.tcl
# YaoGuang SoC FPGA综合脚本

set PART xcvu19p-flva2104-2-i

# 读取源文件
read_verilog -sv ../rtl/soc_top/yaoguang_soc_top.sv
read_verilog -sv ../rtl/ip_rtl/*.sv

# 设置综合选项
synth_design -top yaoguang_soc_top \
    -part $PART \
    -mode out_of_context

# 优化选项
optimize_design -resource

# 报告综合结果
report_utilization -hierarchical
report_timing_summary

# 保存综合结果
write_checkpoint ../checkpoints/synthesis/yaoguang_synth.dcp
```

### 3.4 Emulation编译

```bash
# Palladium编译
cd 06_Verification_CV/emulation/scripts
make compile TARGET=emu PLATFORM=palladium

# 编译选项
# EMU_CONFIG=zynq_based    - 仿真器配置
# PARALLEL_COMP=16         - 并行编译数
# OPT_LEVEL=2              - 优化级别

# 编译状态查看
make status

# 重新编译
make clean
make compile
```

---

## 4. 运行测试

### 4.1 RTL仿真运行

#### 4.1.1 单个测试运行

```bash
# 运行单个测试
cd 06_Verification_CV/emulation/scripts
make run TEST=ddr_basic_read_write SIM=vcs

# 带调试运行
make run TEST=ddr_basic_read_write SIM=vcs DEBUG=1

# 运行并生成波形
make run TEST=ddr_basic_read_write SIM=vcs WAVEFORM=1

# 指定测试时长
make run TEST=interrupt_test SIM=vcs MAX_TIME=100ms
```

#### 4.1.2 批量测试运行

```bash
# 运行测试套件
make run_suite SUITE=boot_tests SIM=vcs

# 运行所有DDR测试
make run_suite SUITE=ddr_tests SIM=vcs PARALLEL=4

# 运行全部测试
make run_all SIM=vcs

# 使用网格调度运行
make run_all SIM=vcs SCHEDULER=lsf QUEUE=cv_queue
```

#### 4.1.3 运行选项

| 选项 | 说明 | 默认值 |
|------|------|-------|
| TEST | 测试名称 | 必需 |
| SIM | 仿真器 | vcs |
| SEED | 随机种子 | 随机 |
| WAVEFORM | 生成波形 | 0 |
| MAX_TIME | 最大仿真时间 | 1ms |
| VERBOSE | 详细输出 | 0 |
| GUI | 打开GUI | 0 |

### 4.2 回归测试运行

```bash
# 进入回归目录
cd 06_Verification_CV/regression

# 运行完整回归
./run_regression.py --config regression.yaml --full

# 运行冒烟测试
./run_regression.py --config regression.yaml --smoke

# 运行特定测试套件
./run_regression.py --config regression.yaml \
    --suite ddr_tests \
    --suite boot_tests

# 运行并生成报告
./run_regression.py --config regression.yaml \
    --suite all \
    --report_format html \
    --output reports/

# 回归脚本示例
```python
#!/usr/bin/env python3
# run_regression.py

import argparse
import subprocess
import yaml
from pathlib import Path

def run_regression(config_file, suite=None, parallel=1):
    """运行回归测试"""
    with open(config_file) as f:
        config = yaml.safe_load(f)
    
    test_suites = config['suites']
    if suite:
        test_suites = {k: v for k, v in test_suites.items() if k in suite}
    
    for suite_name, tests in test_suites.items():
        print(f"Running suite: {suite_name}")
        for test in tests:
            cmd = ['make', 'run', f'TEST={test}', 'SIM=vcs']
            if parallel > 1:
                cmd.extend(['-j', str(parallel)])
            subprocess.run(cmd)

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--config', default='regression.yaml')
    parser.add_argument('--suite', action='append')
    parser.add_argument('--parallel', type=int, default=1)
    args = parser.parse_args()
    run_regression(args.config, args.suite, args.parallel)
```

### 4.3 FPGA测试运行

```bash
# 连接FPGA开发板
cd 06_Verification_CV/fpga/scripts

# 下载比特流
make download BITSTREAM=../bitstreams/yaoguang_v1.0.bit

# 打开串口
make open_uart PORT=/dev/ttyUSB0 BAUD=115200

# 运行FPGA测试
make fpga_test TEST=boot_test

# 运行所有FPGA测试
make fpga_test_all

# 连续运行测试
make fpga_stress_test HOURS=72
```

### 4.4 Emulation测试运行

```bash
# 进入Emulation目录
cd 06_Verification_CV/emulation

# 运行Palladium测试
make run_emu TEST=ddr_bandwidth_test

# 运行性能测试
make run_perf_test

# 运行回归测试
make run_regression_emu

# 监控运行状态
make monitor STATUS_FILE=run_status.json
```

---

## 5. 查看结果

### 5.1 测试结果查看

#### 5.1.1 控制台输出

```bash
# 运行测试后查看结果
cd 06_Verification_CV/emulation/scripts
cat runlogs/ddr_basic_read_write/output.log

# 预期输出示例
[TEST] ddr_basic_read_write
[TIME] 2026-01-18 10:30:15
[STATUS] PASS
[DURATION] 125.432 ms
[DETAILS]
  - Write test: PASS (0 errors)
  - Read test: PASS (0 errors)
  - ECC test: PASS (1-bit error corrected)
  - Bandwidth: 28.5 GB/s
```

#### 5.1.2 结果日志位置

| 测试类型 | 日志目录 |
|---------|---------|
| RTL仿真 | 06_Verification_CV/emulation/runlogs/{test_name}/ |
| FPGA测试 | 06_Verification_CV/fpga/testlogs/ |
| Emulation | 06_Verification_CV/emulation/runlogs/ |
| 回归测试 | 06_Verification_CV/regression/reports/ |

### 5.2 覆盖率报告查看

```bash
# 生成覆盖率报告
make coverage_report

# 查看HTML报告
firefox 06_Verification_CV/coverage_reports/html/index.html

# 命令行查看覆盖率
cat 06_Verification_CV/coverage_reports/summary/coverage_summary.txt

# 覆盖率报告示例
==============================
Code Coverage Summary
==============================
Module: yaoguang_soc_top
------------------------------
Line Coverage:      97.2% (1245/1280)
Branch Coverage:    93.5% (478/511)
Condition Coverage: 96.8% (312/322)
FSM Coverage:       98.1% (156/159)
Toggle Coverage:    94.3% (2456/2604)
------------------------------
Overall Score:      95.9%
```

### 5.3 波形查看

```bash
# 使用Verdi查看波形
verdi -sv testbench.sv -ssrc/top.fsdb &

# 使用GTKWave查看波形
gtkwave testbench.vcd &

# 波形文件位置
ls 06_Verification_CV/emulation/waves/{test_name}/
```

### 5.4 回归报告查看

```bash
# 查看最新回归报告
firefox 06_Verification_CV/regression/reports/latest/index.html

# 命令行查看
cat 06_Verification_CV/regression/reports/latest/regression_summary.txt

# 回归报告示例
==============================
Regression Summary
==============================
Date: 2026-01-18
Suite: Full Regression
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
```

### 5.5 问题跟踪查看

```bash
# 查看问题列表
cat 06_Verification_CV/docs/cv_testplan_detail.md | grep -A 5 "CV-"

# 使用问题跟踪系统
firefox https://jira.example.com/browse/CV-
```

---

## 6. 常见问题

### 6.1 编译问题

#### Q1: VCS编译报"License error"

**问题**: 运行VCS时提示找不到License。

**解决方法**:
```bash
# 检查License设置
lmstat -c 27000@license-server

# 设置正确的License路径
export LM_LICENSE_FILE=27000@license-server

# 如果使用浮动License
export LM_LICENSE_FILE=27000@license-server:27001@backup-server
```

#### Q2: 综合时内存不足

**问题**: FPGA综合过程中内存不足导致失败。

**解决方法**:
```bash
# 增加交换空间
sudo fallocate -l 64G /swapfile
sudo chmod 600 /swapfile
sudo mkswap /swapfile
sudo swapon /swapfile

# 使用增量综合减少内存使用
make synth INCREMENTAL=1
```

#### Q3: 编译速度慢

**问题**: 编译耗时过长。

**解决方法**:
```bash
# 使用并行编译
make compile -j$(nproc)

# 使用增量编译
make compile INCREMENTAL=1

# 清理临时文件
make clean
```

### 6.2 仿真问题

#### Q4: 仿真挂起无响应

**问题**: 仿真运行后长时间无输出。

**解决方法**:
```bash
# 设置最大仿真时间
make run TEST=test_name MAX_TIME=100ms

# 检查是否有死循环
# 在代码中添加打印语句

# 使用波形分析定位问题
make run TEST=test_name WAVEFORM=1
```

#### Q5: 随机测试结果不一致

**问题**: 相同测试多次运行结果不同。

**解决方法**:
```bash
# 使用固定随机种子
make run TEST=test_name SEED=12345

# 在测试代码中设置确定性随机
srandom(12345);
```

#### Q6: 覆盖率收集不完整

**问题**: 部分代码未被覆盖。

**解决方法**:
```bash
# 检查覆盖率配置
cat coverage_config.yaml

# 添加遗漏的测试用例
# 参考coverage_reports/html查看未覆盖代码

# 使用定向测试覆盖未达区域
make run TEST=directed_test
```

### 6.3 FPGA问题

#### Q7: FPGA下载失败

**问题**: 比特流下载到FPGA失败。

**解决方法**:
```bash
# 检查JTAG连接
lsusb | grep Xilinx

# 检查板卡电源
# 确认板卡指示灯正常

# 重启Vivado Hardware Manager
```

#### Q8: FPGA运行不稳定

**问题**: FPGA原型运行一段时间后出现错误。

**解决方法**:
```bash
# 检查时钟稳定性
# 使用示波器测量时钟信号

# 检查温度
# 确认散热风扇正常工作

# 降低运行频率
make synth FREQ=100MHz
```

### 6.4 工具问题

#### Q9: Python依赖缺失

**问题**: 运行Python脚本时提示模块缺失。

**解决方法**:
```bash
# 重新安装Python依赖
pip install -r requirements.txt

# 验证虚拟环境
source cv_venv/bin/activate
python -c "import cv_utils; print('OK')"
```

#### Q10: 权限问题

**问题**: 执行脚本时权限不足。

**解决方法**:
```bash
# 添加执行权限
chmod +x scripts/*.sh

# 使用sudo（如果需要）
sudo ./scripts/flash_fpga.sh
```

### 6.5 联系方式

遇到其他问题请联系：

| 角色 | 联系邮箱 | 负责范围 |
|------|---------|---------|
| CV验证经理 | cv-manager@yaoguang.com | 验证流程、进度 |
| DV验证主管 | dv-lead@yaoguang.com | 模块级验证 |
| FPGA工程师 | fpga-team@yaoguang.com | FPGA原型 |
| Emulation工程师 | emulation@yaoguang.com | 硬件加速仿真 |

---

**文档结束**
