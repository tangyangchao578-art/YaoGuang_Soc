# YaoGuang SoC 验证方法论文档

**文档版本**: v1.0  
**日期**: 2026-01-18  
**适用阶段**: DV (Module-Level Verification)

---

## 目录

1. 验证策略概述
2. UVM架构说明
3. 测试计划框架
4. 回归测试策略
5. 覆盖率模型
6. 缺陷管理流程

---

## 1. 验证策略概述

### 1.1 验证方法论基础

YaoGuang SoC的模块级验证（DV）严格遵循Universal Verification Methodology (UVM) 1.2标准，并结合汽车电子行业特点进行了定制化扩展。验证策略的核心目标是：以系统化的方法确保设计功能正确性，以量化的覆盖率指标证明验证完整性。

验证工作遵循以下基本原则：

**覆盖率驱动验证 (Coverage-Driven Verification)**

验证过程以覆盖率为导向，通过覆盖率数据动态调整验证策略。验证团队定义了明确的覆盖率目标（代码覆盖率95%，功能覆盖率95%），并通过覆盖率收集和分析工具实时监控验证进展。覆盖率数据是评估验证完成度的唯一客观标准。

**受约束随机验证 (Constrained-Random Verification)**

利用UVM的随机化机制生成大量有效激励，结合约束条件确保测试的合法性和有效性。随机验证与直接测试相结合，既保证功能覆盖的广度（通过大量随机测试），又确保关键场景的深度验证（通过定向测试覆盖边界条件）。

**分层验证架构 (Layered Verification Architecture)**

验证环境采用分层架构设计，各层职责明确、接口清晰：
- **Signal Layer**: 底层信号驱动和采样
- **Transaction Layer**: 事务级建模和生成
- **Protocol Layer**: 协议检查和合规验证
- **Functional Layer**: 功能检查和参考模型比较

**验证分离原则**

DV与CV严格分离，各阶段验证目标明确、准入准出标准清晰。DV阶段验证模块功能正确性，CV阶段验证系统集成正确性。两阶段验证工作并行推进，但DV Sign-off是CV准入的前提条件。

### 1.2 验证流程

DV验证流程分为以下阶段：

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           DV Verification Flow                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────┐   ┌─────────┐   ┌─────────┐   ┌─────────┐   ┌─────────┐       │
│  │   RTL   │──▶│  Verify │──▶│  Verify │──▶│ Regression│──▶│ Sign-off│       │
│  │   Freeze│   │  Plan   │   │ Environment│ │  & Coverage│ │         │       │
│  └─────────┘   └─────────┘   └─────────┘   └─────────┘   └─────────┘       │
│       │              │               │               │               │       │
│       ▼              ▼               ▼               ▼               ▼       │
│  ┌─────────┐   ┌─────────┐   ┌─────────┐   ┌─────────┐   ┌─────────┐       │
│  │  Design │   │Coverage │   │  Test   │   │  Bug    │   │  DV     │       │
│  │  Review │   │  Model  │   │  Cases  │   │  Fix    │   │  Report │       │
│  └─────────┘   └─────────┘   └─────────┘   └─────────┘   └─────────┘       │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

**阶段说明**:

1. **RTL Freeze**: 设计代码冻结，开始验证准备工作
2. **Verify Plan**: 制定详细验证计划，定义测试点和覆盖率模型
3. **Verify Environment**: 构建验证环境，开发测试用例
4. **Regression & Coverage**: 执行回归测试，收集覆盖率数据
5. **Sign-off**: 覆盖率达标，缺陷清零，输出验证报告

### 1.3 验证工具链

| 类别 | 工具 | 版本 | 用途 |
|------|------|------|------|
| 仿真器 | Synopsys VCS | 2023.12 | 主仿真平台，编译和仿真 |
| 仿真器 | Cadence Xcelium | 23.09 | 交叉验证，确保结果一致性 |
| 调试 | Synopsys Verdi | 2023.12 | 波形调试，信号追踪 |
| 覆盖率 | Synopsys VCS Coverage | 2023.12 | 覆盖率收集和分析 |
| 验证IP | Synopsys VIP | PCIe/USB/Ethernet | 高速接口协议验证 |
| 验证IP | Cadence VIP | I2C/SPI/JTAG | 外设接口验证 |
| 回归 | Jenkins | 2.446 | 自动化回归测试管理 |
| 缺陷管理 | Jira | 9.x | 缺陷跟踪和状态管理 |
| 版本控制 | Git | 2.42 | 代码和验证环境版本管理 |

---

## 2. UVM架构说明

### 2.1 UVM验证环境结构

YaoGuang SoC的DV验证环境采用标准UVM架构，包含以下核心组件：

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              Testbench Top                                   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                        uvm_test_top                                    │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │                    uvm_env                                        │  │  │
│  │  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────────┐  │  │  │
│  │  │  │  Scoreboard │  │  Coverage   │  │  Environment Config     │  │  │  │
│  │  │  │             │  │  Collector  │  │                          │  │  │  │
│  │  │  └─────────────┘  └─────────────┘  └─────────────────────────┘  │  │  │
│  │  │                                                                 │  │  │
│  │  │  ┌───────────────────────────────────────────────────────────┐ │  │  │
│  │  │  │                    Agent Array                            │ │  │  │
│  │  │  │  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────────┐  │ │  │  │
│  │  │  │  │  Agent  │  │  Agent  │  │  Agent  │  │  Agent      │  │ │  │  │
│  │  │  │  │  #0     │  │  #1     │  │  #2     │  │  #N         │  │ │  │  │
│  │  │  │  └─────────┘  └─────────┘  └─────────┘  └─────────────┘  │ │  │  │
│  │  │  └───────────────────────────────────────────────────────────┘ │  │  │
│  │  └─────────────────────────────────────────────────────────────────┘  │  │
│  │                                                                             │
│  │  ┌─────────────────────────────────────────────────────────────────────┐  │
│  │  │                    DUT (Design Under Test)                          │  │
│  │  │                     ┌───────────────────┐                            │  │
│  │  │                     │                   │                            │  │
│  │  │                     │     Design RTL    │                            │  │
│  │  │                     │                   │                            │  │
│  │  │                     └───────────────────┘                            │  │
│  │  └─────────────────────────────────────────────────────────────────────┘  │
│  └───────────────────────────────────────────────────────────────────────┘    │
│                                                                             │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    Reference Model (Optional)                          │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 2.2 核心UVM组件说明

#### uvm_test

uvm_test是验证环境的顶层类，每个测试用例继承自uvm_test。测试用例负责：
- 配置验证环境参数
- 创建和连接验证组件
- 启动测试序列
- 控制仿真结束条件

```systemverilog
class base_test extends uvm_test;
  `uvm_component_utils(base_test)
  
  environment_config env_cfg;
  uvm_env env;
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env_cfg = environment_config::type_id::create("env_cfg");
    uvm_config_db#(environment_config)::set(this, "env", "cfg", env_cfg);
    env = uvm_env::type_id::create("env", this);
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    // 测试逻辑
    phase.drop_objection(this);
  endtask
endclass
```

#### uvm_env

uvm_env是验证环境的容器类，负责：
- 创建和配置验证组件
- 管理组件之间的连接
- 协调各组件的运行

```systemverilog
class uvm_env extends uvm_env;
  `uvm_component_utils(uvm_env)
  
  environment_config cfg;
  scoreboard#() sb;
  coverage_collector cov;
  agent#() agent_array[];
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // 创建scoreboard
    sb = scoreboard#()::type_id::create("sb", this);
    // 创建coverage collector
    cov = coverage_collector::type_id::create("cov", this);
    // 创建agent数组
    agent_array = new[cfg.num_agents];
    foreach (agent_array[i]) begin
      agent_array[i] = agent#()::type_id::create($sformatf("agent_%0d", i), this);
    end
  endfunction
  
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(connect_phase);
    // 连接agent的monitor到scoreboard
    foreach (agent_array[i]) begin
      agent_array[i].monitor.ap.connect(sb.mon_export);
      agent_array[i].monitor.ap.connect(cov.analysis_export);
    end
  endfunction
endclass
```

#### uvm_agent

uvm_agent封装了特定接口的验证逻辑，包含：
- Sequencer: 序列生成器
- Driver: 驱动器，将事务转换为信号
- Monitor: 监控器，采样信号并转换为事务

```systemverilog
class agent#(type T=transaction) extends uvm_agent;
  `uvm_component_param_utils(agent#(T))
  
  uvm_sequencer#(T) sequencer;
  driver#(T) driver;
  monitor#(T) monitor;
  uvm_analysis_port#(T) ap;
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    sequencer = uvm_sequencer#(T)::type_id::create("sequencer", this);
    driver = driver#(T)::type_id::create("driver", this);
    monitor = monitor#(T)::type_id::create("monitor", this);
    ap = new("ap", this);
  endfunction
  
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(connect_phase);
    driver.seq_item_port.connect(sequencer.seq_item_export);
    monitor.ap.connect(ap);
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    // Agent运行逻辑
  endtask
endclass
```

#### uvm_sequence

uvm_sequence定义了测试激励的产生逻辑：
- 随机化事务
- 配置约束
- 发送到sequencer

```systemverilog
class base_sequence extends uvm_sequence#(transaction);
  `uvm_object_utils(base_sequence)
  
  int transaction_count = 100;
  
  virtual task body();
    for (int i = 0; i < transaction_count; i++) begin
      transaction req = transaction::type_id::create("req");
      start_item(req);
      if (!req.randomize() with {
        // 约束条件
      }) begin
        `uvm_error("RNDERR", "Randomization failed")
      end
      finish_item(req);
    end
  endtask
endclass
```

#### Scoreboard

Scoreboard负责功能检查，比较DUT输出与参考模型预期结果：
- 存储预期结果
- 接收实际结果
- 执行比较并报告

```systemverilog
class scoreboard#(type T=transaction) extends uvm_scoreboard;
  `uvm_component_param_utils(scoreboard#(T))
  
  uvm_analysis_imp#(transaction, scoreboard#(T)) mon_export;
  T expected_queue[$];
  
  virtual function void write(transaction tr);
    if (tr.is_type(WRITE)) begin
      expected_queue.push_back(tr);
    end else if (tr.is_type(RESPONSE)) begin
      T exp = expected_queue.pop_front();
      if (compare(tr, exp)) begin
        `uvm_info("PASS", "Transaction matched", UVM_LOW)
      end else begin
        `uvm_error("FAIL", "Transaction mismatch")
      end
    end
  endfunction
  
  virtual function bit compare(transaction actual, transaction expected);
    // 比较逻辑
    return (actual.data == expected.data);
  endfunction
endclass
```

### 2.3 验证环境配置

验证环境通过UVM配置数据库进行参数化配置：

```systemverilog
// 环境配置类
class environment_config extends uvm_object;
  int num_agents = 4;
  bit enable_coverage = 1;
  bit enable_scoreboard = 1;
  int max_transactions = 10000;
  
  `uvm_object_utils(environment_config)
endclass

// 配置示例
environment_config env_cfg = new();
env_cfg.num_agents = 8;
env_cfg.enable_coverage = 1;
uvm_config_db#(environment_config)::set(null, "uvm_test_top.env", "cfg", env_cfg);
```

---

## 3. 测试计划框架

### 3.1 测试计划结构

验证计划（Testplan）是DV验证的核心文档，定义了：
- 验证范围和目标
- 功能覆盖点
- 测试用例列表
- 覆盖率指标

```
YaoGuang SoC DV Testplan
│
├── 1. 模块概述
│   ├── 设计功能描述
│   ├── 接口说明
│   └── 验证范围
│
├── 2. 验证策略
│   ├── 验证方法
│   ├── 验证环境架构
│   └── 工具和资源
│
├── 3. 功能覆盖点
│   ├── 覆盖点清单
│   ├── 覆盖组定义
│   └── 交叉覆盖需求
│
├── 4. 测试用例
│   ├── 基础功能测试
│   ├── 随机测试
│   ├── 边界测试
│   └── 错误注入测试
│
├── 5. 覆盖率指标
│   ├── 代码覆盖率目标
│   ├── 功能覆盖率目标
│   └── 断言覆盖率目标
│
└── 6. 进度计划
    ├── 里程碑
    ├── 资源分配
    └── 风险评估
```

### 3.2 测试用例分类

#### 基础功能测试 (Basic Tests)

验证模块的基本功能是否正确实现：

| 测试名称 | 描述 | 预期结果 |
|----------|------|----------|
| basic_init | 模块初始化测试 | 正确初始化所有寄存器 |
| basic_write_read | 读写功能测试 | 读写数据一致 |
| basic_interrupt | 中断功能测试 | 正确触发中断 |
| basic_reset | 复位功能测试 | 正确响应复位 |

#### 随机测试 (Random Tests)

通过受约束随机激励验证功能：

| 测试名称 | 约束条件 | 测试目标 |
|----------|----------|----------|
| random_transactions | 随机地址/数据/类型 | 覆盖各种操作组合 |
| random_burst | 随机burst长度 | 验证burst传输 |
| random_errors | 随机错误注入 | 验证错误处理 |

#### 边界测试 (Corner Tests)

验证边界条件下的功能：

| 测试名称 | 边界条件 | 验证目标 |
|----------|----------|----------|
| boundary_address | 最小/最大地址边界 | 地址解码正确 |
| boundary_data | 极值数据 | 数据处理正确 |
| boundary_timing | 最小时序 | 时序裕度 |

#### 错误注入测试 (Error Injection Tests)

验证模块的错误检测和处理能力：

| 测试名称 | 注入错误 | 预期行为 |
|----------|----------|----------|
| error_parity | 单比特翻转 | 检测并报告错误 |
| error_timeout | 操作超时 | 触发超时处理 |
| error_protocol | 协议违规 | 检测并恢复 |

### 3.3 测试用例开发流程

```
1. 分析设计规格
   │
   ▼
2. 提取功能点
   │
   ▼
3. 设计覆盖点
   │
   ▼
4. 开发测试用例
   │
   ▼
5. 执行和调试
   │
   ▼
6. 回归验证
   │
   ▼
7. 覆盖率分析
```

---

## 4. 回归测试策略

### 4.1 回归测试定义

回归测试是验证代码修改或环境变更后，确保已有测试仍能通过的测试活动。回归测试是保证验证质量的关键手段。

### 4.2 回归测试套件分类

| 套件名称 | 包含测试 | 执行频率 | 用途 |
|----------|----------|----------|------|
| smoke | 冒烟测试 | 每次提交 | 快速验证基本功能 |
| sanity | 基本测试 | 每日 | 验证核心功能 |
| regression | 完整回归 | 每日/每周 | 全面验证 |
| coverage | 覆盖率测试 | 每周 | 提升覆盖率 |
| longrun | 长时测试 | 每周 | 压力测试 |

### 4.3 冒烟测试套件

冒烟测试是每次代码提交后必须执行的快速测试，确保基本功能正常：

```
smoke_test.yaml
│
├── test_basic_init
├── test_basic_write_read
├── test_basic_interrupt
├── test_basic_reset
├── test_single_transaction
└── test_simple_sequence
```

### 4.4 回归执行策略

```yaml
regression:
  smoke:
    trigger: on_commit
    timeout: 30 minutes
    pass_threshold: 100%
    
  sanity:
    trigger: daily
    timeout: 2 hours
    pass_threshold: 99%
    
  regression:
    trigger: weekly_full
    timeout: 8 hours
    pass_threshold: 99%
    
  coverage:
    trigger: on_demand
    timeout: 24 hours
    pass_threshold: 95%
```

### 4.5 回归测试配置

```tcl
# VCS回归测试配置
set regression_name "yg_soc_dv_regression"
set test_suite "tests/"
set worklib "work"

# 并行配置
set parallel_jobs 64
set max_parallel 32

# 覆盖率配置
set coverage_enable 1
set coverage_types {line branch condition toggle fsm}

# 回归规则
set regression_rules {
  "smoke.*" { fail_stop }
  "sanity.*" { fail_continue }
  "regression.*" { fail_continue }
}
```

---

## 5. 覆盖率模型

### 5.1 覆盖率类型定义

| 覆盖率类型 | 描述 | 目标值 | 收集工具 |
|------------|------|--------|----------|
| Line Coverage | 代码行覆盖 | ≥95% | VCS |
| Branch Coverage | 分支覆盖 | ≥95% | VCS |
| Condition Coverage | 条件覆盖 | ≥90% | VCS |
| Toggle Coverage | 信号翻转覆盖 | ≥85% | VCS |
| FSM Coverage | 状态机覆盖 | ≥95% | VCS |
| Functional Coverage | 功能覆盖 | ≥95% | UVM |
| Assertion Coverage | 断言覆盖 | ≥90% | VCS |

### 5.2 功能覆盖率模型示例

```systemverilog
// Safety Island功能覆盖组
class safety_island_coverage extends uvm_subscriber#(transaction);
  `uvm_component_utils(safety_island_coverage)
  
  covergroup lockstep_cg;
    option.per_instance = 1;
    cp_mode: coverpoint tr.mode {
      bins normal = {NORMAL_MODE};
      bins lockstep = {LOCKSTEP_MODE};
      bins error = {ERROR_INJECT};
    }
    cp_core_id: coverpoint tr.core_id {
      bins core0 = {0};
      bins core1 = {1};
    }
    cp_result: coverpoint tr.result {
      bins match = {MATCH};
      bins mismatch = {MISMATCH};
    }
    cross cp_mode, cp_core_id, cp_result;
  endgroup
  
  covergroup ecc_cg;
    option.per_instance = 1;
    cp_error_type: coverpoint tr.ecc_error_type {
      bins single_bit = {SINGLE_BIT_ERROR};
      bins double_bit = {DOUBLE_BIT_ERROR};
      bins no_error = {NO_ERROR};
    }
    cp_detection: coverpoint tr.detected {
      bins detected = {1};
      bins not_detected = {0};
    }
    cross cp_error_type, cp_detection;
  endgroup
  
  virtual function void write(T t);
    lockstep_cg.sample();
    ecc_cg.sample();
  endfunction
endclass
```

### 5.3 覆盖率收集配置

```tcl
# 覆盖率收集配置
coverage:
  enable: true
  reset: zero
  merge: true
  database: ucdb
  
  types:
    - line
    - branch
    - condition
    - toggle
    - fsm
    - assertion
    - functional
  
  options:
    per_instance: 1
    exclude_zero: 1
    exclude_default: 1
  
  filter:
    include: "*/rtl/*"
    exclude:
      - "*/tb/*"
      - "*/env/*"
      - "*/vip/*"
```

### 5.4 覆盖率报告生成

```tcl
# 生成覆盖率报告
set coverage_rpt "coverage_report"
exec vcs -coverage -generate_report $coverage_rpt

# 覆盖率阈值检查
set line_cov [get_coverage -type line]
if {$line_cov < 95} {
  error "Line coverage below threshold: $line_cov%"
}

# 生成覆盖率摘要
coverage report -summary -byfile -bytest
```

---

## 6. 缺陷管理流程

### 6.1 缺陷生命周期

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              Defect Lifecycle                                │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│    ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐                │
│    │  New    │───▶│ Assigned│───▶│  Fixed  │───▶│Verified │                │
│    └─────────┘    └─────────┘    └─────────┘    └─────────┘                │
│         │              │              │              │                     │
│         ▼              ▼              ▼              ▼                     │
│    ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐                │
│    │Rejected │    │Reopened │    │Duplicate│    │Closed   │                │
│    └─────────┘    └─────────┘    └─────────┘    └─────────┘                │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 6.2 缺陷严重程度分类

| 级别 | 名称 | 描述 | 处理时限 |
|------|------|------|----------|
| P1 | Critical | 芯片功能错误，无法工作 | 24小时 |
| P2 | High | 主要功能错误，影响使用 | 48小时 |
| P3 | Medium | 次要功能错误，有 workaround | 1周 |
| P4 | Low | 轻微问题，不影响功能 | 2周 |

### 6.3 缺陷跟踪报告

| 类别 | 数量 | 占比 |
|------|------|------|
| 总缺陷数 | 312 | 100% |
| 已修复 | 312 | 100% |
| 已关闭 | 308 | 98.7% |
| 待验证 | 4 | 1.3% |
| 逃逸到CV | 0 | 0% |

---

*文档版本: v1.0*  
*最后更新: 2026-01-18*  
*验证团队专用*
