# NPU Cluster Feature List

## 文档信息

| 项目 | 内容 |
|------|------|
| 模块名称 | npu_cluster |
| 版本 | V1.0 |
| 创建日期 | 2026-01-18 |
| 状态 | Draft |
| 目标 ASIL | ASIL-B |

---

## 1. 计算引擎特性

### 1.1 MAC 阵列

| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| FE_MAC_001 | 1024 INT8 MAC 单元 | P0 | Not Started |
| FE_MAC_002 | 512 FP16 MAC 单元 (可配置模式) | P0 | Not Started |
| FE_MAC_003 | 4 级流水线设计 | P0 | Not Started |
| FE_MAC_004 | INT32 累加精度 (INT8 模式) | P0 | Not Started |
| FE_MAC_005 | FP32 累加精度 (FP16 模式) | P1 | Not Started |
| FE_MAC_006 | 峰值算力: 75 TOPS @ 2.0GHz | P0 | Not Started |

### 1.2 数据精度

| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| FE_DTP_001 | INT8 输入/权重/输出 | P0 | Not Started |
| FE_DTP_002 | INT16 输入/权重/输出 | P1 | Not Started |
| FE_DTP_003 | FP16 输入/权重/输出 | P1 | Not Started |
| FE_DTP_004 | BFP16 支持 | P1 | Not Started |

---

## 2. 片上存储特性

### 2.1 Weight SRAM

| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| FE_WSR_001 | 容量: 2 MB/集群 | P0 | Not Started |
| FE_WSR_002 | 组织: 16 banks x 128 KB | P0 | Not Started |
| FE_WSR_003 | 位宽: 512-bit/bank | P0 | Not Started |
| FE_WSR_004 | 峰值带宽: 256 GB/s | P0 | Not Started |
| FE_WSR_005 | 访问延迟: 5-10 cycles | P0 | Not Started |
| FE_WSR_006 | SECDED ECC 保护 | P1 | Not Started |
| FE_WSR_007 | 权重压缩 (2-4x 压缩率) | P1 | Not Started |
| FE_WSR_008 | 预加载引擎 | P1 | Not Started |

### 2.2 Activation SRAM

| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| FE_ASR_001 | 容量: 2 MB/集群 | P0 | Not Started |
| FE_ASR_002 | 组织: 16 banks x 128 KB | P0 | Not Started |
| FE_ASR_003 | 位宽: 512-bit/bank | P0 | Not Started |
| FE_ASR_004 | 峰值带宽: 256 GB/s | P0 | Not Started |
| FE_ASR_005 | 访问延迟: 5-10 cycles | P0 | Not Started |
| FE_ASR_006 | SECDED ECC 保护 | P1 | Not Started |
| FE_ASR_007 | 双缓冲 (乒乓操作) | P0 | Not Started |

### 2.3 Output Buffer

| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| FE_OBF_001 | 容量: 1 MB/集群 | P0 | Not Started |
| FE_OBF_002 | 组织: 8 banks x 128 KB | P0 | Not Started |
| FE_OBF_003 | 位宽: 512-bit/bank | P0 | Not Started |
| FE_OBF_004 | 峰值带宽: 128 GB/s | P0 | Not Started |
| FE_OBF_005 | 访问延迟: 3-5 cycles | P0 | Not Started |

---

## 3. 计算单元特性

### 3.1 矩阵乘法单元

| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| FE_MMU_001 | INT8 矩阵乘法 | P0 | Not Started |
| FE_MMU_002 | FP16 矩阵乘法 | P1 | Not Started |
| FE_MMU_003 | Winograd 优化 | P1 | Not Started |
| FE_MMU_004 | Im2Col 变换 | P1 | Not Started |
| FE_MMU_005 | GEMM 通用矩阵乘法 | P0 | Not Started |

### 3.2 激活函数单元

| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| FE_ACT_001 | ReLU 激活函数 | P0 | Not Started |
| FE_ACT_002 | PReLU 激活函数 | P1 | Not Started |
| FE_ACT_003 | SiLU 激活函数 | P1 | Not Started |
| FE_ACT_004 | GeLU 激活函数 | P1 | Not Started |
| FE_ACT_005 | Sigmoid 激活函数 | P1 | Not Started |
| FE_ACT_006 | Tanh 激活函数 | P1 | Not Started |
| FE_ACT_007 | Swish 激活函数 | P1 | Not Started |
| FE_ACT_008 | Batch Normalization | P0 | Not Started |
| FE_ACT_009 | Layer Normalization | P1 | Not Started |

### 3.3 池化单元

| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| FE_POL_001 | Max Pooling | P0 | Not Started |
| FE_POL_002 | Average Pooling | P0 | Not Started |
| FE_POL_003 | Global Pooling | P1 | Not Started |
| FE_POL_004 | 可配置 Stride | P0 | Not Started |
| FE_POL_005 | 可配置 Padding | P0 | Not Started |
| FE_POL_006 | 可配置 Kernel Size | P0 | Not Started |

---

## 4. 稀疏计算特性

| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| FE_SPR_001 | 结构化稀疏 (2:4 模式) | P1 | Not Started |
| FE_SPR_002 | 结构化稀疏 (4:8 模式) | P1 | Not Started |
| FE_SPR_003 | 非结构化稀疏 | P1 | Not Started |
| FE_SPR_004 | 稀疏编码器 | P1 | Not Started |
| FE_SPR_005 | 稀疏解码器 | P1 | Not Started |
| FE_SPR_006 | 零值跳过的控制逻辑 | P1 | Not Started |
| FE_SPR_007 | 压缩表 (32 KB) | P1 | Not Started |
| FE_SPR_008 | 有效算力提升 1.5-2x | P1 | Not Started |

---

## 5. 网络支持特性

### 5.1 网络类型

| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| FE_NNW_001 | CNN 完整支持 | P0 | Not Started |
| FE_NNW_002 | Transformer 完整支持 | P0 | Not Started |
| FE_NNW_003 | RNN/LSTM 完整支持 | P0 | Not Started |
| FE_NNW_004 | MoE (Mixture of Experts) 完整支持 | P1 | Not Started |

### 5.2 卷积算子

| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| FE_CNV_001 | Conv1D | P0 | Not Started |
| FE_CNV_002 | Conv2D | P0 | Not Started |
| FE_CNV_003 | Conv3D | P1 | Not Started |
| FE_CNV_004 | Depthwise Convolution | P0 | Not Started |
| FE_CNV_005 | Separable Convolution | P1 | Not Started |

### 5.3 注意力算子

| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| FE_ATT_001 | Self-Attention | P0 | Not Started |
| FE_ATT_002 | Multi-Head Attention | P0 | Not Started |
| FE_ATT_003 | FlashAttention | P1 | Not Started |

---

## 6. 数据流特性

### 6.1 数据复用

| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| FE_DFR_001 | 权重复用 (8-16x 带宽节省) | P0 | Not Started |
| FE_DFR_002 | 激活复用 (4-8x 带宽节省) | P0 | Not Started |
| FE_DFR_003 | 累加复用 (2-4x 带宽节省) | P0 | Not Started |

### 6.2 数据预取

| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| FE_PRF_001 | 顺序预取 (8 tiles) | P0 | Not Started |
| FE_PRF_002 | 跨步预取 (4 tiles) | P1 | Not Started |
| FE_PRF_003 | 指令预取 (16 instructions) | P0 | Not Started |

---

## 7. DMA 引擎特性

| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| FE_DMA_001 | AXI4 主接口 | P0 | Not Started |
| FE_DMA_002 | 读请求位宽: 256-bit | P0 | Not Started |
| FE_DMA_003 | 读响应位宽: 512-bit | P0 | Not Started |
| FE_DMA_004 | 写请求位宽: 512-bit | P0 | Not Started |
| FE_DMA_005 | 权重加载 (100 GB/s) | P0 | Not Started |
| FE_DMA_006 | 激活加载 (80 GB/s) | P0 | Not Started |
| FE_DMA_007 | 输出存储 (60 GB/s) | P0 | Not Started |
| FE_DMA_008 | 突发传输支持 | P0 | Not Started |

---

## 8. 控制与调度特性

### 8.1 指令集

| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| FE_INS_001 | CONV 指令 | P0 | Not Started |
| FE_INS_002 | MATMUL 指令 | P0 | Not Started |
| FE_INS_003 | FC 指令 | P0 | Not Started |
| FE_INS_004 | ACTIVATION 指令 | P0 | Not Started |
| FE_INS_005 | POOL 指令 | P0 | Not Started |
| FE_INS_006 | MOVE 指令 | P0 | Not Started |
| FE_INS_007 | LOOP 指令 | P0 | Not Started |
| FE_INS_008 | BRANCH 指令 | P1 | Not Started |

### 8.2 调度器

| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| FE_SCH_001 | 张量操作调度 | P0 | Not Started |
| FE_SCH_002 | 循环嵌套生成 | P0 | Not Started |
| FE_SCH_003 | 指令解码 | P0 | Not Started |
| FE_SCH_004 | 指令发射 | P0 | Not Started |
| FE_SCH_005 | 资源分配 | P0 | Not Started |
| FE_SCH_006 | 依赖检查 | P0 | Not Started |

---

## 9. 接口特性

### 9.1 NoC 接口

| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| FE_NOC_001 | AXI4 协议支持 | P0 | Not Started |
| FE_NOC_002 | 读请求 (256-bit, 64 GB/s) | P0 | Not Started |
| FE_NOC_003 | 读响应 (512-bit, 128 GB/s) | P0 | Not Started |
| FE_NOC_004 | 写请求 (512-bit, 128 GB/s) | P0 | Not Started |
| FE_NOC_005 | 写响应 (32-bit, 8 GB/s) | P0 | Not Started |

### 9.2 中断接口

| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| FE_INT_001 | 计算完成中断 (中优先级) | P0 | Not Started |
| FE_INT_002 | 错误中断 (高优先级) | P0 | Not Started |
| FE_INT_003 | 看门狗中断 (最高优先级) | P1 | Not Started |

---

## 10. 安全特性

| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| FE_SAF_001 | Weight SRAM ECC 保护 | P1 | Not Started |
| FE_SAF_002 | Activation SRAM ECC 保护 | P1 | Not Started |
| FE_SAF_003 | 配置寄存器 ECC | P1 | Not Started |
| FE_SAF_004 | 看门狗超时检测 | P1 | Not Started |
| FE_SAF_005 | AXI 协议检查 | P1 | Not Started |
| FE_SAF_006 | BIST 永久故障检测 | P1 | Not Started |
| FE_SAF_007 | 重复计算瞬态故障检测 | P1 | Not Started |
| FE_SAF_008 | 配置范围检查 | P1 | Not Started |

---

## 11. 功耗管理特性

| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| FE_PWR_001 | MAC 阵列时钟门控 | P1 | Not Started |
| FE_PWR_002 | 电源门控 (集群级) | P1 | Not Started |
| FE_PWR_003 | SRAM 低功耗模式 | P1 | Not Started |
| FE_PWR_004 | 电压缩放控制 | P1 | Not Started |
| FE_PWR_005 | 空闲状态检测 | P1 | Not Started |

---

## 12. 验证规格

### 12.1 覆盖率目标

| 指标 | 目标值 |
|------|--------|
| 功能覆盖率 | 100% |
| 代码覆盖率 | >= 95% |
| 断言覆盖率 | >= 90% |

### 12.2 验证用例规划

| 类别 | 用例数 |
|------|--------|
| 算子测试 | 200+ |
| 网络测试 | 50+ |
| 稀疏测试 | 50+ |
| 异常测试 | 100+ |
| 性能测试 | 30+ |

---

## 13. 模块列表

| 模块名称 | 功能描述 | 优先级 |
|----------|----------|--------|
| npu_cluster_top | NPU Cluster 顶层集成 | P0 |
| npu_core | 单个 NPU Core | P0 |
| matrix_mult_unit | 矩阵乘法单元 | P0 |
| activation_unit | 激活函数单元 | P0 |
| pooling_unit | 池化单元 | P0 |
| tensor_buffer | 张量缓存 | P0 |
| dma_engine | DMA 引擎 | P0 |

---

**文档版本**: V1.0  
**创建日期**: 2026-01-18  
**状态**: Draft - 等待 DV 评审
