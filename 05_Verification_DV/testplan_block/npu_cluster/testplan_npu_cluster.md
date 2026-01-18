# NPU Cluster 验证计划

| 文档版本 | V1.0 |
|---------|------|
| 创建日期 | 2026-01-18 |
| 状态 | 进行中 |
| ASIL 等级 | ASIL-B |

---

## 1. 模块概述

### 1.1 功能描述
NPU Cluster 是 YaoGuang SoC 的神经网络处理单元，包含 4 个 Cluster，支持 300 TOPS 算力。

### 1.2 验证范围
- Tensor Buffer
- Matrix Multiplication Unit
- Activation Unit
- Pooling Unit
- Data Flow Controller

---

## 2. 测试点列表

### 2.1 张量运算测试

| ID | 测试点 | 优先级 | 类型 | 期望结果 |
|----|--------|--------|------|----------|
| NPU-TEN-001 | INT8 矩阵乘 | P0 | 功能 | 结果正确 |
| NPU-TEN-002 | INT16 矩阵乘 | P0 | 功能 | 结果正确 |
| NPU-TEN-003 | FP16 矩阵乘 | P0 | 功能 | 结果正确 |
| NPU-TEN-004 | 稀疏加速 | P1 | 功能 | 加速生效 |
| NPU-TEN-005 | 量化支持 | P1 | 功能 | 正确 |

### 2.2 激活函数测试

| ID | 测试点 | 优先级 | 类型 | 期望结果 |
|----|--------|--------|------|----------|
| NPU-ACT-001 | ReLU | P0 | 功能 | 正确 |
| NPU-ACT-002 | Sigmoid | P0 | 功能 | 正确 |
| NPU-ACT-003 | Tanh | P1 | 功能 | 正确 |
| NPU-ACT-004 | Leaky ReLU | P1 | 功能 | 正确 |

### 2.3 池化测试

| ID | 测试点 | 优先级 | 类型 | 期望结果 |
|----|--------|--------|------|----------|
| NPU-POOL-001 | Max Pooling | P0 | 功能 | 正确 |
| NPU-POOL-002 | Avg Pooling | P0 | 功能 | 正确 |
| NPU-POOL-003 | Global Pooling | P1 | 功能 | 正确 |

### 2.4 性能测试

| ID | 测试点 | 优先级 | 类型 | 期望结果 |
|----|--------|--------|------|----------|
| NPU-PERF-001 | TOPS 达成 | P0 | 性能 | ≥ 300 TOPS |
| NPU-PERF-002 | 延迟测试 | P0 | 性能 | 延迟符合 |
| NPU-PERF-003 | 能效比 | P1 | 性能 | 符合规格 |

---

## 3. 验证环境

### 3.1 UVM 环境结构

```
npu_cluster_tb/
├── npu_cluster_env.sv
├── npu_cluster_agent.sv
├── npu_cluster_scoreboard.sv
├── npu_cluster_coverage.sv
└── npu_cluster_assertions.sv
```

### 3.2 测试激励

- 随机张量输入
- 参考模型对比
- 神经网络模型验证

---

## 4. 覆盖率要求

| 覆盖率类型 | 目标 |
|------------|------|
| 代码覆盖率 | ≥ 95% |
| 功能覆盖率 | 100% |
| 断言覆盖率 | ≥ 90% |

---

## 5. 测试用例清单

| 用例名称 | 对应测试点 | 优先级 |
|----------|------------|--------|
| test_int8_matmul | NPU-TEN-001 | P0 |
| test_int16_matmul | NPU-TEN-002 | P0 |
| test_fp16_matmul | NPU-TEN-003 | P0 |
| test_activation | NPU-ACT-001~004 | P0 |
| test_pooling | NPU-POOL-001~003 | P0 |
| test_performance | NPU-PERF-001~003 | P0 |

---

**创建日期**: 2026-01-18
