# YaoGuang SoC DV 验证环境

## 概述

本文档描述 YaoGuang 车规级 SoC 芯片的模块级验证 (DV) 环境。

## 验证范围

### 需要验证的模块

| 序号 | 模块名称 | 优先级 | ASIL 等级 | 验证状态 |
|------|----------|--------|-----------|----------|
| 1 | Safety Island | P0 | ASIL-D | 进行中 |
| 2 | NPU Cluster (4x) | P0 | ASIL-B | 进行中 |
| 3 | CPU Subsystem | P0 | ASIL-B | 计划中 |
| 4 | PMU | P0 | ASIL-D | 已交付 |
| 5 | ISP | P1 | ASIL-B | 计划中 |
| 6 | Memory Controller | P0 | ASIL-B | 计划中 |
| 7 | L3 Cache | P1 | ASIL-B | 计划中 |
| 8 | NoC Interconnect | P0 | ASIL-B | 计划中 |
| 9 | PCIe Controller | P1 | QM | 计划中 |
| 10 | Ethernet Controller | P1 | QM | 计划中 |
| 11 | USB Controller | P1 | QM | 计划中 |
| 12 | Display Controller | P2 | QM | 计划中 |
| 13 | Audio Controller | P2 | QM | 计划中 |
| 14 | CAN FD Controller | P1 | ASIL-B | 计划中 |
| 15 | I2C/SPI/GPIO | P2 | QM | 计划中 |
| 16 | Crypto Engine | P1 | ASIL-B | 计划中 |
| 17 | Debug Subsystem | P2 | QM | 计划中 |

## 验证环境结构

```
05_Verification_DV/
├── dv_plan.md                 # 验证计划
├── uvm_env/                   # UVM 验证环境
│   ├── scripts/              # 运行脚本
│   │   ├── run_dv.py
│   │   └── run_sim.sh
│   ├── src/                  # 源码
│   │   ├── pkg/             # 包定义
│   │   └── component/       # UVM 组件
│   └── vip/                  # 验证 IP
├── testplan_block/           # 测试计划
│   ├── safety_island/
│   ├── npu_cluster/
│   ├── cpu_subsystem/
│   ├── pmu/
│   └── ...
├── tests/                    # 测试用例
├── regression/               # 回归测试
│   └── regression_config.yaml
└── coverage_reports/         # 覆盖率报告
```

## 快速开始

### 1. 编译验证环境

```bash
cd 05_Verification_DV/uvm_env
./scripts/run_sim.sh compile
```

### 2. 运行单个测试

```bash
./scripts/run_sim.sh run -t test_sanity
```

### 3. 运行回归测试

```bash
./scripts/run_dv.py regression nightly
```

### 4. 收集覆盖率

```bash
./scripts/run_dv.py coverage
```

## 覆盖率目标

| 覆盖率类型 | 目标 |
|------------|------|
| 行覆盖率 | ≥ 95% |
| 分支覆盖率 | ≥ 95% |
| 条件覆盖率 | ≥ 90% |
| 翻转覆盖率 | ≥ 90% |
| 状态机覆盖率 | 100% |
| 断言覆盖率 | ≥ 90% |
| 功能覆盖率 | 100% |

## 里程碑

| 里程碑 | 日期 | 交付物 |
|--------|------|--------|
| 验证环境就绪 | 2026-06-15 | UVM 环境、VIP |
| Safety Island Sign-off | 2026-08-31 | 覆盖率报告 |
| NPU Sign-off | 2026-09-30 | 覆盖率报告 |
| 其他模块 Sign-off | 2026-10-31 | 覆盖率报告 |
| DV 验证通过 | 2026-11-30 | 最终验证报告 |

## 验证策略

1. **分层验证**: 从模块级到子系统级
2. **随机验证**: 约束随机测试覆盖边界条件
3. **形式验证**: 关键模块使用形式验证
4. **硬件加速**: 大规模回归使用 Emulation

## 测试点分解

### Safety Island 测试点 (59个)

- 双核锁步处理器: 9个测试点
- ECC 内存控制器: 8个测试点
- 看门狗: 8个测试点
- 故障注入: 5个测试点
- 错误报告: 5个测试点
- 时钟复位监控: 7个测试点
- 电源管理: 4个测试点

### NPU Cluster 测试点 (17个)

- 张量运算: 6个测试点
- 激活函数: 4个测试点
- 池化操作: 4个测试点
- 性能测试: 3个测试点

### PMU 测试点 (28个)

- 电源域控制: 5个测试点
- 监控功能: 4个测试点
- DVFS: 4个测试点
- 低功耗模式: 7个测试点
- 保护功能: 5个测试点

## 回归测试

### Sanity (每次提交)
- 运行时间: < 5分钟
- 测试用例: 50个
- 通过率: 100%

### Nightly (每日)
- 运行时间: < 2小时
- 测试用例: 500个
- 通过率: 95%

### Weekly (每周)
- 运行时间: < 8小时
- 测试用例: 2000个
- 通过率: 90%

### Full (发布前)
- 运行时间: < 24小时
- 测试用例: 5000个
- 通过率: 85%

## 工具链

- **仿真器**: VCS / Xcelium / Questa
- **波形查看**: Verdi
- **覆盖率**: URG / IMC
- **回归管理**: Python + YAML

## 联系人

- DV 验证工程师
- 前端设计工程师
- 架构师
