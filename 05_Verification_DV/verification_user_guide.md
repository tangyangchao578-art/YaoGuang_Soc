# YaoGuang SoC 验证环境使用指南

**文档版本**: v1.0  
**日期**: 2026-01-18  
**适用对象**: 验证工程师、设计工程师

---

## 目录

1. 环境概述
2. 环境搭建步骤
3. 编译命令
4. 运行测试
5. 查看覆盖率
6. 常见问题
7. 调试技巧

---

## 1. 环境概述

### 1.1 验证环境架构

YaoGuang SoC DV验证环境基于UVM 1.2构建，支持Synopsys VCS和Cadence Xcelium双仿真平台。环境采用模块化设计，各IP模块拥有独立的验证环境和测试用例。

```
YaoGuang_SoC/
│
├── 05_Verification_DV/
│   ├── uvm_env/                    # UVM环境源码
│   │   ├── agents/                 # 验证代理
│   │   ├── sequences/              # 测试序列
│   │   ├── scoreboards/            # 计分板
│   │   ├── coverage/               # 覆盖率收集器
│   │   └── env_configs/            # 环境配置
│   │
│   ├── testplan_block/             # 模块测试计划
│   │   ├── safety_island/
│   │   ├── npu_cluster/
│   │   ├── pmu/
│   │   └── ...
│   │
│   ├── tests/                      # 测试用例
│   │   ├── base_tests/             # 基础测试
│   │   ├── directed_tests/         # 定向测试
│   │   └── random_tests/           # 随机测试
│   │
│   ├── regression/                 # 回归配置
│   │   ├── regression.yaml         # 回归套件定义
│   │   ├── run_regression.sh       # 回归运行脚本
│   │   └── post_process/           # 后处理脚本
│   │
│   └── work/                       # 编译工作库
│
└── 04_Design_RTL/                  # 设计代码
    ├── ip_rtl/
    └── soc_top/
```

### 1.2 工具要求

| 工具 | 版本 | 用途 |
|------|------|------|
| VCS | 2023.12 | 主仿真器 |
| Verdi | 2023.12 | 波形调试 |
| Python | 3.9+ | 脚本支持 |
| Git | 2.42+ | 版本控制 |

---

## 2. 环境搭建步骤

### 2.1 获取源码

```bash
# 克隆验证环境仓库
git clone git@gitlab.yaoguang.com:dv/verification_env.git
cd verification_env

# 切换到项目分支
git checkout yaoguang_dv_v1.0

# 初始化子模块
git submodule update --init --recursive
```

### 2.2 设置环境变量

```bash
# 设置VCS环境
export VCS_HOME=/opt/synopsys/vcs/VCS-2023.12
export PATH=$VCS_HOME/bin:$PATH

# 设置Verdi环境
export VERDI_HOME=/opt/synopsys/verdi/Verdi-2023.12
export PATH=$VERDI_HOME/bin:$PATH

# 设置工作目录
export YG_WORK=/path/to/yaoguang_work
export YG_DV_ROOT=/path/to/YaoGuang_Soc/05_Verification_DV

# 设置仿真选项
export SYNOPSYS_SYN=dcp
export LD_LIBRARY_PATH=$VCS_HOME/lib:$LD_LIBRARY_PATH
```

### 2.3 创建工作目录

```bash
# 创建编译工作库
mkdir -p $YG_WORK/work
cd $YG_WORK/work

# 创建仿真结果目录
mkdir -p $YG_WORK/sim_results
mkdir -p $YG_WORK/coverage
mkdir -p $YG_WORK/waves
```

### 2.4 编译验证库

```bash
cd $YG_DV_ROOT
./build_env.sh --clean --compile
```

---

## 3. 编译命令

### 3.1 完整编译

```bash
# 编译整个验证环境
cd $YG_WORK
make clean
make all
```

### 3.2 增量编译

```bash
# 仅编译修改的模块
cd $YG_WORK
make build MODULE=safety_island

# 编译特定测试
cd $YG_WORK
make test TEST=base_test
```

### 3.3 编译选项

```bash
# 使用Verdi调试模式编译
cd $YG_WORK
make debug SIM=vcs

# 使用UCLI调试模式
cd $YG_WORK
make ucli SIM=vcs

# 生成覆盖率数据
cd $YG_WORK
make coverage SIM=vcs
```

### 3.4 Makefile选项

```makefile
# 常用make目标
all:          # 完整编译
clean:        # 清理编译文件
build:        # 编译验证环境
compile:      # 编译设计
sim:          # 运行仿真
regression:   # 运行回归
coverage:     # 收集覆盖率
debug:        # 编译调试版本
help:         # 显示帮助
```

### 3.5 编译脚本示例

```bash
#!/bin/bash
# run_compile.sh - 完整编译脚本

set -e

export SIM=vcs
export TEST=test_basic
export MODULE=all

echo "========================================="
echo "YaoGuang SoC DV Verification Build"
echo "========================================="

cd $YG_WORK

# 清理旧编译
make clean

# 编译UVM库
echo "Compiling UVM library..."
make uvm_lib

# 编译设计
echo "Compiling design..."
make compile

# 编译测试
echo "Compiling test: $TEST"
make build TEST=$TEST

echo "========================================="
echo "Build completed successfully!"
echo "========================================="
```

---

## 4. 运行测试

### 4.1 运行单个测试

```bash
cd $YG_WORK
make sim TEST=test_basic_init
```

### 4.2 运行测试变体

```bash
# 运行带随机种子的测试
cd $YG_WORK
make sim TEST=test_random SEED=12345

# 运行带不同配置的测试
cd $YG_WORK
make sim TEST=test_config CFG=high_perf

# 运行多次迭代
cd $YG_WORK
make sim TEST=test_robust ITERATIONS=100
```

### 4.3 仿真选项

```bash
# 设置仿真时间
make sim TEST=test_basic SIM_TIME=100us

# 启用波形生成
make sim TEST=test_basic WAVES=1

# 启用详细日志
make sim TEST=test_basic VERBOSE=1 LOG_LEVEL=debug
```

### 4.4 仿真脚本示例

```bash
#!/bin/bash
# run_sim.sh - 运行仿真脚本

set -e

export TEST=${1:-test_basic_init}
export SEED=${2:-$(date +%s)}
export WAVES=${3:-0}
export UCLI=${4:-0}

cd $YG_WORK

echo "========================================="
echo "Running Test: $TEST"
echo "Seed: $SEED"
echo "========================================="

# 运行仿真
if [ $WAVES -eq 1 ]; then
    make sim TEST=$TEST SEED=$SEED WAVES=1
elif [ $UCLI -eq 1 ]; then
    make ucli TEST=$TEST SEED=$SEED
else
    make sim TEST=$TEST SEED=$SEED
fi

echo "========================================="
echo "Simulation completed!"
echo "========================================="
```

### 4.5 回归测试运行

```bash
# 运行冒烟测试
cd $YG_DV_ROOT/regression
./run_regression.sh --suite smoke

# 运行Sanity测试
cd $YG_DV_ROOT/regression
./run_regression.sh --suite sanity

# 运行完整回归
cd $YG_DV_ROOT/regression
./run_regression.sh --suite full --parallel 32

# 运行特定模块回归
cd $YG_DV_ROOT/regression
./run_regression.sh --module safety_island
```

### 4.6 回归配置示例

```yaml
# regression.yaml
regression_name: yaoguang_dv_regression

global:
  work_dir: /path/to/work
  sim: vcs
  seed: random

suites:
  smoke:
    tests:
      - test_basic_init
      - test_basic_write_read
      - test_basic_interrupt
      - test_basic_reset
    timeout: 30min
    parallel: 16
    
  sanity:
    tests:
      - test_*
    timeout: 2hr
    parallel: 32
    
  full:
    tests:
      - *
    timeout: 8hr
    parallel: 64
```

---

## 5. 查看覆盖率

### 5.1 生成覆盖率报告

```bash
# 生成完整覆盖率报告
cd $YG_WORK
make coverage_report

# 生成模块级覆盖率报告
cd $YG_WORK
make coverage_report MODULE=safety_island

# 生成HTML报告
cd $YG_WORK
make coverage_html
```

### 5.2 覆盖率查看命令

```bash
# 查看命令行覆盖率摘要
cd $YG_WORK
urg -dir cov_work -report cov_report

# 查看详细覆盖率
cd $YG_WORK
dve -cov -dir cov_work &
```

### 5.3 覆盖率类型过滤

```bash
# 仅查看代码行覆盖率
cd $YG_WORK
urg -dir cov_work -report -bytest -only line

# 仅查看功能覆盖率
cd $YG_WORK
urg -dir cov_work -report -bytest -only functional

# 查看所有覆盖率类型
cd $YG_WORK
urg -dir cov_work -report -full
```

### 5.4 覆盖率检查脚本

```bash
#!/bin/bash
# check_coverage.sh - 检查覆盖率是否达标

set -e

COV_THRESHOLD=95
MODULE=${1:-all}

cd $YG_WORK

echo "========================================="
echo "Coverage Check for Module: $MODULE"
echo "========================================="

# 生成覆盖率报告
make coverage_report MODULE=$MODULE

# 检查覆盖率
LINE_COV=$(grep "Line Coverage" cov_report/summary.txt | awk '{print $3}')
BRANCH_COV=$(grep "Branch Coverage" cov_report/summary.txt | awk '{print $3}')
FUNC_COV=$(grep "Functional Coverage" cov_report/summary.txt | awk '{print $3}')

echo "Line Coverage: $LINE_COV%"
echo "Branch Coverage: $BRANCH_COV%"
echo "Functional Coverage: $FUNC_COV%"

# 检查是否达标
if [ ${LINE_COV%.*} -ge $COV_THRESHOLD ] && \
   [ ${BRANCH_COV%.*} -ge $COV_THRESHOLD ] && \
   [ ${FUNC_COV%.*} -ge $COV_THRESHOLD ]; then
    echo "========================================="
    echo "Coverage PASSED"
    echo "========================================="
    exit 0
else
    echo "========================================="
    echo "Coverage FAILED"
    echo "========================================="
    exit 1
fi
```

### 5.5 Verdi覆盖率查看

```bash
# 使用Verdi查看覆盖率
verdi -cov -dir cov_work -ssf waves.fsdb &
```

---

## 6. 常见问题

### Q1: 编译报错 "UVM not found"

**问题**: 编译时提示找不到UVM库

**解决方案**:
```bash
# 检查UVM_HOME环境变量
echo $UVM_HOME

# 确保UVM库已编译
cd $YG_WORK
make uvm_lib

# 检查VCS版本是否支持UVM
vcs -help | grep uvm
```

### Q2: 仿真挂起无响应

**问题**: 仿真运行但不结束

**解决方案**:
```bash
# 增加仿真超时时间
make sim TEST=test_basic TIMEOUT=3600

# 检查是否有死锁
# 使用Verdi查看波形
verdi -ssf waves.fsdb &

# 检查日志中的循环
grep -r "loop" sim.log
```

### Q3: 覆盖率不增加

**问题**: 运行测试但覆盖率不增长

**解决方案**:
```bash
# 检查覆盖率收集是否启用
make sim TEST=test_basic COVERAGE=1

# 检查覆盖率数据库
ls -la cov_work/

# 重新运行测试
make clean
make sim TEST=test_basic COVERAGE=1
```

### Q4: 随机测试不可重复

**问题**: 相同种子产生不同结果

**解决方案**:
```bash
# 使用固定种子
make sim TEST=test_random SEED=12345

# 检查随机数生成器
grep "srandom" testbench.sv

# 确保编译一致
make clean
make all
```

### Q5: Verdi无法打开波形

**问题**: Verdi打开fsdb文件报错

**解决方案**:
```bash
# 检查fsdb文件是否存在
ls -la waves.fsdb

# 检查Verdi版本
verdi -version

# 重新生成波形
make sim TEST=test_basic WAVES=1
```

---

## 7. 调试技巧

### 7.1 波形调试

```bash
# 生成波形文件
make sim TEST=test_basic WAVES=1

# 使用Verdi打开波形
verdi -ssf waves.fsdb -sv testbench.sv &
```

### 7.2 UCLI调试模式

```bash
# 进入UCLI调试模式
make ucli TEST=test_basic

# UCLI常用命令
# 查看信号
add wave *
run 100ns
step
break add -line 100
run
```

### 7.3 日志调试

```bash
# 生成详细日志
make sim TEST=test_basic VERBOSE=debug LOG_LEVEL=debug

# 搜索错误
grep -i error sim.log

# 搜索警告
grep -i warning sim.log

# 查看特定模块日志
grep -i "module_name" sim.log
```

### 7.4 调试断点

```systemverilog
// 在代码中添加调试断点
`ifdef DEBUG
  $display("[DEBUG] Transaction: %s", req.convert2string());
  $display("[DEBUG] Time: %0t", $time);
`endif

// 使用UVM调试
`uvm_info("DEBUG", $sformatf("Transaction: %0d", trans), UVM_LOW)
```

### 7.5 内存调试

```bash
# 检查内存使用
top -p $(pgrep simv)

# 生成内存快照
make sim TEST=test_basic MEM_SNAPSHOT=1
```

---

## 8. 快速参考

### 常用命令速查表

| 命令 | 说明 |
|------|------|
| `make clean` | 清理编译文件 |
| `make all` | 完整编译 |
| `make sim TEST=test_basic` | 运行测试 |
| `make sim TEST=test_basic SEED=12345` | 指定种子运行 |
| `make coverage` | 收集覆盖率 |
| `make coverage_report` | 生成覆盖率报告 |
| `make ucli` | 进入调试模式 |
| `./run_regression.sh --suite smoke` | 运行冒烟测试 |

### 环境变量速查表

| 变量 | 说明 | 示例值 |
|------|------|--------|
| VCS_HOME | VCS安装路径 | /opt/synopsys/vcs/VCS-2023.12 |
| VERDI_HOME | Verdi安装路径 | /opt/synopsys/verdi/Verdi-2023.12 |
| YG_WORK | 工作目录 | /path/to/work |
| YG_DV_ROOT | DV根目录 | /path/to/YaoGuang_Soc/05_Verification_DV |
| SIM | 仿真器 | vcs |
| TEST | 测试名称 | test_basic_init |

---

*文档版本: v1.0*  
*最后更新: 2026-01-18*  
*如有问题，请联系验证团队*
