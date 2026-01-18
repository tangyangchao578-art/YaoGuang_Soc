# GPU Feature List

## 文档信息

| 项目 | 内容 |
|------|------|
| 版本 | V1.0 |
| 日期 | 2026-01-19 |
| 状态 | 草稿 |
| 来源 | 02_Architecture/10_GPU_Microarchitecture.md |

---

## 1. 性能指标

| 指标 | 目标值 | 说明 |
|------|--------|------|
| **FP32 算力** | ≥ 2 TFLOPS | 2核总计 |
| **FP16 算力** | ≥ 4 TFLOPS | 加速模式 |
| **INT8 算力** | ≥ 8 TOPS | 量化推理 |
| **工作频率** | 1.0-1.5 GHz | DVFS |
| **核心数量** | 2 | Shader Core |
| **EU 数量** | 64 (32 EU/核) | 执行单元 |
| **ALU 数量** | 256 (128 EU) | 算术逻辑单元 |
| **功耗预算** | ≤ 7W | 峰值 |
| **面积预算** | ≤ 8 mm² | 约占7% |

---

## 2. API 支持

| API | 支持 | 版本 |
|-----|------|------|
| **Vulkan** | 是 | 1.2 |
| **OpenCL** | 是 | 3.0 |
| **OpenGL ES** | 是 | 3.2 |
| **DirectX 12** | 否 | 移动端优化 |

---

## 3. 渲染管线特性

| 阶段 | 模块 | 功能 |
|------|------|------|
| **Vertex Shader** | Shader Core | 顶点变换 |
| **Tessellation** | Shader Core | 曲面细分 |
| **Geometry Shader** | Shader Core | 几何处理 |
| **Rasterization** | Rasterizer | 光栅化 |
| **Early Z** | Depth/Stencil | 深度测试 |
| **Fragment Shader** | Shader Core | 片段着色 |
| **Late Z** | Depth/Stencil | 深度测试 |
| **Blending** | ROP | 颜色混合 |

---

## 4. 缓存层次

| 层级 | 大小 | 关联度 | 特性 |
|------|------|--------|------|
| **L1 Texture** | 64 KB/EU | 4-way | 256-bit/cycle |
| **L1 Uniform** | 32 KB/EU | 4-way | 128-bit/cycle |
| **L1 Load/Store** | 32 KB/EU | 4-way | 256-bit/cycle |
| **L2 Cache** | 2 MB | 16-way | ECC保护, 128-bit/cycle |

---

## 5. 子模块清单

| 模块名 | 功能 | 文件 |
|--------|------|------|
| **gpu_top** | 顶层集成 | gpu_top.sv |
| **shader_core_x2** | 2个渲染核心 | shader_core_x2.sv |
| **vertex_processor** | 顶点处理器 | vertex_processor.sv |
| **fragment_processor** | 片元处理器 | fragment_processor.sv |
| **texture_mapping_unit** | 纹理映射单元 | texture_mapping_unit.sv |
| **rasterizer** | 光栅化单元 | rasterizer.sv |
| **depth_stencil_unit** | 深度/模板测试 | depth_stencil_unit.sv |
| **framebuffer_controller** | 帧缓冲控制 | framebuffer_controller.sv |

---

## 6. 接口规格

| 接口 | 协议 | 位宽 | 特性 |
|------|------|------|------|
| **系统接口** | ACE4 | 256-bit | 缓存一致性 |
| **内存带宽** | - | - | 64 GB/s (双向) |
| **中断** | - | - | Job Complete, GPU Fault, Context Fault |

---

## 7. 执行单元 (EU) 规格

| 功能 | 吞吐量 | 延迟 |
|------|--------|------|
| **FP32 ADD** | 2 ops/cycle | 4 cycles |
| **FP32 MUL** | 2 ops/cycle | 5 cycles |
| **FP32 FMA** | 2 ops/cycle | 6 cycles |
| **INT32 ADD** | 2 ops/cycle | 1 cycle |
| **INT32 MUL** | 2 ops/cycle | 3 cycles |
| **FP16 FMA** | 4 ops/cycle | 6 cycles |
| **INT8 MAD** | 8 ops/cycle | 4 cycles |

---

## 8. 功耗管理特性

| 技术 | 应用 | 效果 |
|------|------|------|
| **时钟门控** | 空闲 EU | 30-40% 节能 |
| **频率缩放** | DVFS | 10-20% 节能 |
| **电压缩放** | 动态电压 | 10-15% 节能 |
| **模块关断** | 未使用模块 | 40-60% 节能 |

---

## 9. 安全特性

| 特性 | 支持 | ASIL等级 |
|------|------|----------|
| **地址校验** | 是 | ASIL-B |
| **ECC保护** | L2 Cache | ASIL-B |
| **看门狗** | 作业超时 | ASIL-B |
| **内存保护** | MMU | ASIL-B |

---

## 10. 验证目标

| 验证类型 | 覆盖率目标 |
|----------|------------|
| **功能覆盖率** | 100% |
| **代码覆盖率** | 100% |
| **图形测试** | 200+ 用例 |
| **计算测试** | 100+ 用例 |
| **异常测试** | 100+ 用例 |

---

**版本**: V1.0
**日期**: 2026-01-19
