# 功能安全案例模板

## 1. 管理摘要

**项目名称**: {{PROJECT_NAME}}
**ASIL等级**: ASIL{{ASIL_LEVEL}}
**标准版本**: ISO 26262:2018
**文档版本**: {{VERSION}}
**日期**: {{DATE}}

### 安全目标概述

| 安全目标ID | 描述 | ASIL | FTTI | 安全状态 |
|-----------|------|------|------|----------|
| SG-001 | {{SAFETY_GOAL_1}} | ASIL D | 10ms | {{SAFE_STATE}} |
| SG-002 | {{SAFETY_GOAL_2}} | ASIL D | 10ms | {{SAFE_STATE}} |

### 合规性总结

| 安全指标 | 目标值 | 实际值 | 合规 |
|---------|--------|--------|------|
| SPFM | ≥ 99% | {{ACTUAL_SPFM}}% | ✓/✗ |
| LFM | ≥ 90% | {{ACTUAL_LFM}}% | ✓/✗ |
| PMHF | < 0.1 FIT | {{ACTUAL_PMHF}} FIT | ✓/✗ |
| 诊断覆盖率 | ≥ 99% | {{ACTUAL_DC}}% | ✓/✗ |

### 主要结论

{{MAIN_CONCLUSIONS}}

---

## 2. 引言

### 2.1 范围

本文档描述{{PROJECT_NAME}}的功能安全案例，证明设计满足ISO 26262:2018的要求，特别是ASIL{{ASIL_LEVEL}}等级要求。

### 2.2 系统描述

{{SYSTEM_DESCRIPTION}}

### 2.3 适用标准

- ISO 26262:2018 - 道路车辆功能安全
- IEC 61508 - 功能安全基础标准
- AEC-Q100 - 汽车集成电路应力测试
- MISRA-C - C编码标准

---

## 3. 功能安全要求

### 3.1 安全目标

| 安全目标ID | 描述 | ASIL | FTTI | 安全状态 |
|-----------|------|------|------|----------|
| SG-001 | {{SAFETY_GOAL_1_DESC}} | ASIL D | 10ms | {{SAFE_STATE}} |
| SG-002 | {{SAFETY_GOAL_2_DESC}} | ASIL D | 10ms | {{SAFE_STATE}} |

### 3.2 功能安全要求（FSR）

#### FSR-001: {{FSR_001_DESC}}

- **ID**: FSR-001
- **描述**: {{FSR_001_DESC}}
- **ASIL等级**: ASIL D
- **FTTI**: 10ms
- **安全状态**: {{SAFE_STATE}}
- **安全机制**: 
  - {{SAFETY_MECHANISM_1}}
  - {{SAFETY_MECHANISM_2}}

#### FSR-002: {{FSR_002_DESC}}

- **ID**: FSR-002
- **描述**: {{FSR_002_DESC}}
- **ASIL等级**: ASIL D
- **FTTI**: 10ms
- **安全状态**: {{SAFE_STATE}}
- **安全机制**: 
  - {{SAFETY_MECHANISM_3}}
  - {{SAFETY_MECHANISM_4}}

### 3.3 安全状态定义

| 安全状态 | 触发条件 | 恢复方法 |
|---------|---------|----------|
| {{SAFE_STATE_1}} | {{TRIGGER_1}} | {{RECOVERY_1}} |
| {{SAFE_STATE_2}} | {{TRIGGER_2}} | {{RECOVERY_2}} |

---

## 4. 系统架构

### 4.1 系统架构概述

```
┌─────────────────────────────────────────┐
│          ECU System                     │
│  ┌─────────────┐  ┌─────────────┐      │
│  │   Safety    │  │   Main      │      │
│  │   Core      │  │   Core      │      │
│  │   (ASIL D)  │  │   (QM)      │      │
│  └──────┬──────┘  └──────┬──────┘      │
│         │                │             │
│  ┌──────▼────────────────▼──────┐      │
│  │       安全互连               │      │
│  └──────┬────────────────┬──────┘      │
│         │                │             │
│  ┌──────▼──────┐ ┌──────▼──────┐      │
│  │ 安全存储器  │ │ 主存储器    │      │
│  └─────────────┘ └─────────────┘      │
└─────────────────────────────────────────┘
```

### 4.2 硬件架构

**主要组件：**
- CPU: ARM Cortex-R52 (Dual-core Lockstep)
- SRAM: 1MB with ECC (SECDED)
- Flash: 4MB with ECC
- Safety Watchdog: Window watchdog
- Power Monitor: Voltage and current monitoring
- Clock Monitor: Clock loss and frequency monitoring

### 4.3 软件架构

**安全相关软件：**
- Safety Monitor
- Error Handling
- Safety State Management
- Diagnostic Reporting

---

## 5. 安全分析

### 5.1 危害分析和风险评估（HARA）

| 危害ID | 危害描述 | 严重度 | 暴露率 | 可控性 | ASIL |
|--------|---------|--------|--------|--------|------|
| H-001 | {{HAZARD_1}} | S3 | E4 | C3 | ASIL D |
| H-002 | {{HAZARD_2}} | S3 | E4 | C2 | ASIL D |

### 5.2 FMEA（失效模式与影响分析）

参见附件A：FMEA报告

**主要发现：**
- 高优先级失效模式: {{HIGH_PRIORITY_COUNT}} (RPN > 200)
- 中优先级失效模式: {{MEDIUM_PRIORITY_COUNT}} (100 < RPN ≤ 200)
- 低优先级失效模式: {{LOW_PRIORITY_COUNT}} (RPN ≤ 100)

### 5.3 FTA（故障树分析）

参见附件B：FTA报告

**关键故障路径：**
1. {{FAULT_PATH_1}}
2. {{FAULT_PATH_2}}
3. {{FAULT_PATH_3}}

### 5.4 FMEDA（失效模式、影响和诊断分析）

参见附件C：FMEDA报告

**组件可靠性数据：**

| 组件 | FIT率 | 诊断覆盖率 | 安全影响 |
|------|--------|-----------|----------|
| CPU | 10.0 | 95.0% | Unsafe |
| SRAM | 100.0 | 99.0% | Safe |
| Flash | 50.0 | 98.0% | Safe |
| Watchdog | 1.0 | 99.0% | Safe |
| Power Monitor | 5.0 | 95.0% | Safe |
| Clock Monitor | 5.0 | 95.0% | Safe |

**安全指标：**

| 指标 | 目标值 | 实际值 | 合规 |
|------|--------|--------|------|
| SPFM | ≥ 99% | {{ACTUAL_SPFM}}% | ✓/✗ |
| LFM | ≥ 90% | {{ACTUAL_LFM}}% | ✓/✗ |
| PMHF | < 0.1 FIT | {{ACTUAL_PMHF}} FIT | ✓/✗ |
| 平均DC | ≥ 99% | {{ACTUAL_DC}}% | ✓/✗ |

---

## 6. 安全机制

### 6.1 预防机制

| 机制ID | 描述 | 目标故障 | 检测时间 |
|--------|------|----------|----------|
| PM-001 | Lockstep Dual-core | CPU故障 | 1个时钟周期 |
| PM-002 | ECC (SECDED) | 内存故障 | 立即检测 |
| PM-003 | 周期内存检查 | 潜伏故障 | 周期性 |

### 6.2 检测机制

| 机制ID | 描述 | 目标故障 | 检测时间 |
|--------|------|----------|----------|
| DM-001 | 看门狗 | 软件挂起 | 10ms |
| DM-002 | 电源监控 | 电源故障 | 5ms |
| DM-003 | 时钟监控 | 时钟故障 | 2ms |

### 6.3 控制机制

| 机制ID | 描述 | 触发条件 | 响应时间 |
|--------|------|----------|----------|
| CM-001 | ECU复位 | 检测到致命故障 | < 1ms |
| CM-002 | 安全状态切换 | 检测到可恢复故障 | < FTTI |
| CM-003 | 故障日志 | 检测到任何故障 | 立即 |

---

## 7. 验证和确认

### 7.1 验证方法

| 验证ID | 方法 | 覆盖率 | 结果 |
|--------|------|--------|------|
| V-001 | 功能测试 | 100% | 通过 |
| V-002 | 故障注入 | 95% | 通过 |
| V-003 | 性能测试 | 100% | 通过 |
| V-004 | 可靠性测试 | 100% | 通过 |

### 7.2 验证结果

参见附件D：验证报告

**关键结果：**
- 故障覆盖率: {{FAULT_COVERAGE}}%
- 诊断覆盖率: {{DIAGNOSTIC_COVERAGE}}%
- 所有测试通过: ✓

### 7.3 确认

| 确认活动 | 方法 | 结果 | 证据 |
|---------|------|------|------|
| 安全目标确认 | 审查 | 通过 | 确认报告 |
| 功能安全要求确认 | 审查 | 通过 | 确认报告 |
| 安全机制确认 | 测试 | 通过 | 测试报告 |
| 第三方评估 | 独立评估 | 通过 | 评估报告 |

---

## 8. 生产

### 8.1 生产测试

| 测试类型 | 覆盖率 | 通过率 |
|---------|--------|--------|
| ATE测试 | 95% | {{ATE_PASS_RATE}}% |
| 功能测试 | 100% | {{FT_PASS_RATE}}% |
| BIST测试 | 100% | {{BIST_PASS_RATE}}% |
| 可靠性测试 | 100% | {{RELIABILITY_PASS_RATE}}% |

### 8.2 生产监控

| 监控参数 | 目标值 | 实际值 | 合规 |
|---------|--------|--------|------|
| 良品率 | > 99% | {{ACTUAL_YIELD}}% | ✓/✗ |
| 失效率 | < 100 PPM | {{ACTUAL_FAILURE_RATE}} PPM | ✓/✗ |
| 工艺Cp | > 1.33 | {{ACTUAL_CP}} | ✓/✗ |

### 8.3 质量控制

- SPC统计过程控制
- 定期质量审计
- 根本原因分析
- 纠正和预防措施

---

## 9. 附录

### 附录A：FMEA报告
- 附件：fmea_report.pdf

### 附录B：FTA报告
- 附件：fta_report.pdf

### 附录C：FMEDA报告
- 附件：fmeda_report.pdf

### 附录D：验证报告
- 附件：verification_report.pdf

### 附录E：安全机制描述
- 附件：safety_mechanisms.pdf

### 附录F：生产计划
- 附件：production_plan.pdf

### 附录G：运行监控计划
- 附件：field_monitoring_plan.pdf

---

## 10. 结论

基于上述分析和验证，{{PROJECT_NAME}}满足ISO 26262:2018 ASIL{{ASIL_LEVEL}}的所有要求。

**主要结论：**
- ✓ 所有安全目标已定义并满足ASIL{{ASIL_LEVEL}}要求
- ✓ 所有功能安全要求已实现并验证
- ✓ 所有安全指标达到或超过目标值
- ✓ 所有安全机制已实现并验证
- ✓ 所有验证和确认活动已完成并成功
- ✓ 生产计划已定义并实施
- ✓ 功能安全案例完整且可信

**批准：**

| 角色 | 姓名 | 签名 | 日期 |
|------|------|------|------|
| 功能安全经理 | {{FSM_NAME}} | | |
| 系统工程师 | {{SE_NAME}} | | |
| 硬件工程师 | {{HW_NAME}} | | |
| 软件工程师 | {{SW_NAME}} | | |
| 质量经理 | {{QM_NAME}} | | |
