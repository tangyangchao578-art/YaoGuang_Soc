# ISP Feature List

## 文档信息

| 项目 | 内容 |
|------|------|
| 文档版本 | V1.0 |
| 创建日期 | 2026-01-19 |
| 状态 | 已批准 |
| 交付对象 | DV 验证团队 |

---

## 1. 规格概述

| 指标 | 目标值 | 备注 |
|------|--------|------|
| **摄像头输入** | 16 路 MIPI CSI-2 | 可配置 8/16 lanes |
| **分辨率** | 4K @ 60fps | 单路最大 |
| **总带宽** | 64 GB/s | 16 路 x 4K/30fps |
| **功耗预算** | ≤ 4W | 峰值 |
| **面积预算** | ≤ 4 mm² | 约占 3% |
| **延迟** | < 10 ms | 端到端处理 |
| **安全等级** | ASIL-B | 功能安全 |

---

## 2. 输入接口 Feature

### 2.1 MIPI CSI-2 RX

| Feature ID | Feature 描述 | 优先级 | 验证重点 |
|------------|--------------|--------|----------|
| INP-001 | 支持 D-PHY v1.2 / C-PHY v1.2 | P0 | PHY 兼容性 |
| INP-002 | 8-16 Lane 可配置 | P0 | Lane 切换 |
| INP-003 | 4.5 Gbps/lane 速率 | P0 | 吞吐量 |
| INP-004 | RAW8/10/12/14/16 格式 | P0 | 格式解析 |
| INP-005 | 4 虚拟通道 | P1 | VC 路由 |
| INP-006 | Packet 错误检测与纠正 | P0 | CRC 检查 |
| INP-007 | Lane 极性反转 | P1 | PCB 布局灵活性 |
| INP-008 | 嵌入式数据提取 | P2 | Metadata 获取 |

---

## 3. 图像处理 Pipeline Feature

### 3.1 Sensor Correction

| Feature ID | Feature 描述 | 优先级 | 验证重点 |
|------------|--------------|--------|----------|
| COR-001 | Black Level Correction (±64 LSB) | P0 | 暗电流校正 |
| COR-002 | Defect Pixel Correction (梯度检测) | P0 | 死像素修复 |
| COR-003 | Lens Shading Correction (17x17 LUT) | P1 | 暗角校正 |
| COR-004 | 固定/自适应模式切换 | P1 | 模式覆盖 |

### 3.2 Color Processing

| Feature ID | Feature 描述 | 优先级 | 验证重点 |
|------------|--------------|--------|----------|
| COL-001 | Demosaic (高级自适应算法) | P0 | Bayer→RGB 转换 |
| COL-002 | Color Correction Matrix (3x3, 12-bit) | P0 | 色彩准确性 |
| COL-003 | Gamma Encoding (2.2, 256-segment LUT) | P0 | 伽马曲线 |
| COL-004 | 固定/自适应 CCM 模式 | P1 | 模式切换 |

### 3.3 Enhancement

| Feature ID | Feature 描述 | 优先级 | 验证重点 |
|------------|--------------|--------|----------|
| ENH-001 | 2D/3D Noise Reduction | P0 | 时域+空域降噪 |
| ENH-002 | Sharpening (非锐化掩膜) | P1 | 边缘增强 |
| ENH-003 | 可配置降噪强度 | P1 | 参数覆盖 |
| ENH-004 | 可配置锐化强度/阈值 | P2 | 参数覆盖 |

### 3.4 HDR Processing

| Feature ID | Feature 描述 | 优先级 | 验证重点 |
|------------|--------------|--------|----------|
| HDR-001 | 2-4 帧 HDR Fusion | P1 | 多帧融合 |
| HDR-002 | 最大 16x 曝光比 | P1 | 宽动态范围 |
| HDR-003 | 权重图融合算法 | P1 | 融合质量 |
| HDR-004 | 单帧 HDR 模式 | P2 | 模式覆盖 |

---

## 4. 统计模块 Feature

### 4.1 AE (Auto Exposure)

| Feature ID | Feature 描述 | 优先级 | 验证重点 |
|------------|--------------|--------|----------|
| STA-001 | 16x16 分区统计 | P1 | 区域划分 |
| STA-002 | 亮度直方图 | P1 | 直方图准确性 |
| STA-003 | Y 通道统计输出 | P1 | 数据正确性 |
| STA-004 | 每帧更新 | P1 | 时序正确性 |

### 4.2 AWB (Auto White Balance)

| Feature ID | Feature 描述 | 优先级 | 验证重点 |
|------------|--------------|--------|----------|
| STA-005 | 32x32 分区统计 | P1 | 区域划分 |
| STA-006 | R/G/B 累加统计 | P1 | 数据正确性 |
| STA-007 | 色温估计 | P2 | 算法准确性 |
| STA-008 | CCM 建议输出 | P2 | 参数建议 |

### 4.3 Histogram

| Feature ID | Feature 描述 | 优先级 | 验证重点 |
|------------|--------------|--------|----------|
| STA-009 | 256 bins x 4 channels | P1 | 直方图精度 |
| STA-010 | 可配置 ROI | P2 | 区域选择 |
| STA-011 | 帧/区域累积 | P2 | 累积功能 |

---

## 5. 输出接口 Feature

### 5.1 输出格式

| Feature ID | Feature 描述 | 优先级 | 验证重点 |
|------------|--------------|--------|----------|
| OUT-001 | RAW16 输出 (16 bit) | P0 | 格式正确性 |
| OUT-002 | RGB24 输出 (24 bit) | P0 | 色彩完整性 |
| OUT-003 | RGB30 输出 (30 bit) | P1 | 高动态范围 |
| OUT-004 | YUV422 输出 (16 bit) | P1 | 格式正确性 |
| OUT-005 | YUV420 输出 (12 bit) | P2 | 格式正确性 |

### 5.2 输出目标

| Feature ID | Feature 描述 | 优先级 | 验证重点 |
|------------|--------------|--------|----------|
| OUT-006 | AXI4 Memory 接口 (32 GB/s) | P0 | 内存写入 |
| OUT-007 | AXI4 NPU 接口 (64 GB/s) | P1 | 数据转发 |
| OUT-008 | DPI/DCI Display 接口 (16 GB/s) | P2 | 显示输出 |

---

## 6. 性能 Feature

### 6.1 处理能力

| Feature ID | Feature 描述 | 优先级 | 验证重点 |
|------------|--------------|--------|----------|
| PER-001 | 4K@60fps 单路处理 | P0 | 帧率达成 |
| PER-002 | 4 路 4K@30fps 并行 | P1 | 并行处理 |
| PER-003 | 1080p@120fps 处理 | P1 | 高帧率支持 |
| PER-004 | 720p@240fps 处理 | P2 | 高帧率支持 |

### 6.2 延迟要求

| Feature ID | Feature 描述 | 优先级 | 验证重点 |
|------------|--------------|--------|----------|
| PER-005 | Sensor Interface < 2 lines | P1 | 延迟测量 |
| PER-006 | Pipeline < 64 lines | P1 | 延迟测量 |
| PER-007 | Output Formatter < 4 lines | P1 | 延迟测量 |
| PER-008 | 端到端 < 10ms | P0 | 端到端延迟 |

---

## 7. 功能安全 Feature

| Feature ID | Feature 描述 | 优先级 | 验证重点 |
|------------|--------------|--------|----------|
| SAF-001 | ASIL-B 合规 | P0 | 安全认证 |
| SAF-002 | ECC 保护 (L1/L2 Cache) | P0 | 错误检测 |
| SAF-003 | 双核锁步 (Safety Island) | P0 | 冗余校验 |
| SAF-004 | 看门狗定时器 | P1 | 超时检测 |
| SAF-005 | 错误注入测试接口 | P1 | 验证覆盖 |

---

## 8. 可配置性 Feature

| Feature ID | Feature 描述 | 优先级 | 验证重点 |
|------------|--------------|--------|----------|
| CFG-001 | Pipeline 顺序可配置 | P1 | 顺序切换 |
| CFG-002 | 模块 bypass 功能 | P1 | 绕过验证 |
| CFG-003 | 寄存器映射 (APB/AXI) | P0 | 寄存器访问 |
| CFG-004 | 固件更新接口 | P2 | 固件升级 |

---

## 9. 验证准入标准

### 9.1 DV 准入条件

| 条件 | 要求 | 状态 |
|------|------|------|
| Feature List 交付 | 本文档 | ✅ 已交付 |
| RTL 代码冻结 | 2026-07-31 | ⏳ 待完成 |
| 代码覆盖率 | ≥ 95% | ⏳ 待验证 |
| 功能覆盖率 | 100% | ⏳ 待验证 |
| 回归测试通过率 | 100% | ⏳ 待验证 |

### 9.2 验证重点优先级

1. **P0 (必须通过)**: INP-*, COR-001, COR-002, COL-001, COL-002, COL-003, ENH-001, OUT-*, PER-001, PER-008, SAF-*, CFG-003
2. **P1 (建议通过)**: 剩余 Feature
3. **P2 (可选)**: 增强功能

---

## 10. 交付物清单

| 交付物 | 位置 | 状态 |
|--------|------|------|
| 微架构规格 | 02_Architecture/09_ISP_Microarchitecture.md | ✅ 已完成 |
| Feature List | 04_Design_RTL/ip_rtl/isp/FEATURE_LIST.md | ✅ 本文档 |
| RTL 代码 | 04_Design_RTL/ip_rtl/isp/*.sv | ✅ 已完成 |
| SDC 约束 | 04_Design_RTL/ip_rtl/isp/isp.sdc | ✅ 已完成 |
| UVM 验证环境 | 05_Verification_DV/ | ⏳ 待开始 |

---

**文档版本**: V1.0  
**批准日期**: 2026-01-19  
**交付对象**: DV 验证团队
**交付日期**: 2026-01-19
**签名**: ________________
