# Display 子系统 Feature List

**文档版本**: v1.0  
**创建日期**: 2026-01-18  
**模块**: Display Subsystem  
**状态**: 待评审

---

## 1. 顶层模块 (display_top)

### 1.1 系统接口
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| TOP-SYS-001 | 系统时钟接口（100-200MHz） | P0 | Pending |
| TOP-SYS-002 | 异步复位接口，支持同步释放 | P0 | Pending |
| TOP-SYS-003 | 中断输出接口（int_display） | P1 | Pending |

### 1.2 NoC 从接口
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| TOP-AXI-001 | AXI4-Lite 从接口，32bit 地址宽度 | P0 | Pending |
| TOP-AXI-002 | 读写响应支持（OKAY, SLVERR, DECERR） | P0 | Pending |
| TOP-AXI-003 | 字节、半字、字访问粒度 | P1 | Pending |

### 1.3 AXI 主接口
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| TOP-MAXI-001 | AXI4 主接口，64bit 数据宽度 | P0 | Pending |
| TOP-MAXI-002 | 支持 INCR 和 FIXED 突发类型 | P0 | Pending |
| TOP-MAXI-003 | 最大突发长度 16 | P1 | Pending |
| TOP-MAXI-004 | 支持 8 outstanding 交易 | P1 | Pending |

### 1.4 外部接口
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| TOP-EXT-001 | HDMI 2.1 接口（3 通道 TMDS + 时钟） | P0 | Pending |
| TOP-EXT-002 | DisplayPort 1.4a 接口（4 通道 + AUX） | P0 | Pending |
| TOP-EXT-003 | MIPI DSI-2 接口（4 通道 D-PHY） | P1 | Pending |
| TOP-EXT-004 | 热插拔检测（HPD）支持 | P1 | Pending |

---

## 2. 显示引擎 (display_engine)

### 2.1 时序生成
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| ENG-TMG-001 | 可配置水平时序参数 | P0 | Pending |
| ENG-TMG-002 | 可配置垂直时序参数 | P0 | Pending |
| ENG-TMG-003 | 可编程像素时钟频率 | P0 | Pending |
| ENG-TMG-004 | 支持隔行扫描模式 | P2 | Pending |
| ENG-TMG-005 | 可编程同步极性 | P1 | Pending |
| ENG-TMG-006 | 支持 7680×4320@60Hz 分辨率 | P0 | Pending |

### 2.2 帧缓冲管理
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| ENG-FB-001 | Ping-pong 双缓冲机制 | P0 | Pending |
| ENG-FB-002 | 可配置帧缓冲基地址 | P0 | Pending |
| ENG-FB-003 | 可配置帧缓冲行跨度（Stride） | P0 | Pending |
| ENG-FB-004 | 帧开始/行开始信号输出 | P1 | Pending |
| ENG-FB-005 | 欠载检测和错误报告 | P1 | Pending |

### 2.3 多通道支持
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| ENG-MUL-001 | 多显示输出同步启动 | P1 | Pending |
| ENG-MUL-002 | 独立分辨率配置 | P1 | Pending |
| ENG-MUL-003 | 帧率转换支持 | P2 | Pending |
| ENG-MUL-004 | 画面拼接支持 | P2 | Pending |

---

## 3. 帧缓冲读取器 (framebuffer_reader)

### 3.1 内存访问
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| FB-axi-001 | AXI4 突发读取优化 | P0 | Pending |
| FB-axi-002 | 数据预取机制 | P1 | Pending |
| FB-axi-003 | 总线带宽效率优化 | P1 | Pending |
| FB-axi-004 | 内存访问超时保护 | P2 | Pending |

### 3.2 像素格式支持
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| FB-FMT-001 | RGB888 格式支持 | P0 | Pending |
| FB-FMT-002 | RGB565 格式支持 | P0 | Pending |
| FB-FMT-003 | RGBA8888 格式支持 | P0 | Pending |
| FB-FMT-004 | YUV422 格式支持 | P1 | Pending |
| FB-FMT-005 | YUV420 格式支持 | P1 | Pending |
| FB-FMT-006 | 端序配置（小端/大端） | P2 | Pending |
| FB-FMT-007 | R/B 通道交换支持 | P2 | Pending |

---

## 4. 色彩处理流水线 (color_processing)

### 4.1 色彩空间转换
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| CP-CSC-001 | RGB to YCbCr BT.601 转换 | P0 | Pending |
| CP-CSC-002 | RGB to YCbCr BT.709 转换 | P0 | Pending |
| CP-CSC-003 | RGB to YCbCr BT.2020 转换 | P1 | Pending |
| CP-CSC-004 | YCbCr to RGB 转换 | P1 | Pending |
| CP-CSC-005 | 可配置转换系数 | P2 | Pending |

### 4.2 HDR 处理
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| CP-HDR-001 | HDR10 格式支持 | P0 | Pending |
| CP-HDR-002 | HLG 格式支持 | P1 | Pending |
| CP-HDR-003 | PQ 伽马曲线支持 | P1 | Pending |
| CP-HDR-004 | 色调映射（Tone Mapping） | P0 | Pending |
| CP-HDR-005 | 动态元数据支持 | P2 | Pending |

### 4.3 伽马校正
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| CP-GMM-001 | BT.1886（2.4 伽马） | P0 | Pending |
| CP-GMM-002 | sRGB（2.2 伽马） | P0 | Pending |
| CP-GMM-003 | 可编程伽马 LUT | P1 | Pending |
| CP-GMM-004 | 多段线性逼近 | P2 | Pending |

### 4.4 色彩增强
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| CP-ENH-001 | 动态对比度增强（DCE） | P2 | Pending |
| CP-ENH-002 | 自适应饱和度控制 | P2 | Pending |
| CP-ENH-003 | 肤色保护 | P2 | Pending |
| CP-ENH-004 | 降噪处理 | P2 | Pending |

### 4.5 宽色域映射
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| CP-GMT-001 | BT.2020 to BT.709 映射 | P0 | Pending |
| CP-GMT-002 | DCI-P3 支持 | P1 | Pending |
| CP-GMT-003 | 色域裁剪和缩放 | P1 | Pending |

### 4.6 抖动处理
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| CP-DTH-001 | 蓝色噪声抖动 | P1 | Pending |
| CP-DTH-002 | 误差扩散抖动 | P2 | Pending |
| CP-DTH-003 | 低色深输出支持 | P1 | Pending |

---

## 5. HDMI 2.1 发送器 (hdmi_tx)

### 5.1 TMDS 编码
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| HDMI-ENC-001 | 8b/10b TMDS 编码 | P0 | Pending |
| HDMI-ENC-002 | 控制字符编码 | P0 | Pending |
| HDMI-ENC-003 | 数据岛编码 | P1 | Pending |

### 5.2 视频时序
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| HDMI-TMG-001 | DE 信号生成 | P0 | Pending |
| HDMI-TMG-002 | HSYNC/VSYNC 生成 | P0 | Pending |
| HDMI-TMG-003 | 像素数据使能 | P1 | Pending |

### 5.3 分辨率支持
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| HDMI-RES-001 | 7680×4320@60Hz (DSC) | P0 | Pending |
| HDMI-RES-002 | 3840×2160@120Hz | P0 | Pending |
| HDMI-RES-003 | 1920×1080@240Hz | P1 | Pending |

### 5.4 HDMI 特性
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| HDMI-FTR-001 | 动态 HDR 支持 | P1 | Pending |
| HDMI-FTR-002 | VRR 可变刷新率 | P2 | Pending |
| HDMI-FTR-003 | ALLM 自动低延迟 | P2 | Pending |
| HDMI-FTR-004 | eARC 音频回传 | P3 | Pending |

---

## 6. DisplayPort 1.4a 发送器 (dp_tx)

### 6.1 Main Link 编码
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| DP-ENC-001 | 8b/10b Main Link 编码 | P0 | Pending |
| DP-ENC-002 | 通道扰码（Scrambler） | P0 | Pending |
| DP-ENC-003 | 训练序列生成 | P1 | Pending |

### 6.2 视频传输
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| DP-VID-001 | 视频包生成 | P0 | Pending |
| DP-VID-002 | 填充包生成 | P1 | Pending |
| DP-VID-003 | MSA（Main Stream Attribute） | P1 | Pending |

### 6.3 分辨率支持
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| DP-RES-001 | 7680×4320@60Hz (DSC) | P0 | Pending |
| DP-RES-002 | 5120×2880@120Hz (DSC) | P1 | Pending |
| DP-RES-003 | 多流传输（MST） | P2 | Pending |

### 6.4 DisplayPort 特性
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| DP-FTR-001 | DSC 显示流压缩 | P1 | Pending |
| DP-FTR-002 | FEC 前向纠错 | P2 | Pending |
| DP-FTR-003 | 自适应同步 | P2 | Pending |
| DP-FTR-004 | AUX 通道通信 | P1 | Pending |

---

## 7. MIPI DSI-2 发送器 (mipi_dsi_tx)

### 7.1 D-PHY 物理层
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| DSI-PHY-001 | 4 通道 D-PHY 支持 | P0 | Pending |
| DSI-PHY-002 | HS 高速模式（4.5Gbps/通道） | P0 | Pending |
| DSI-PHY-003 | LP 低功耗模式 | P1 | Pending |
| DSI-PHY-004 | 时钟通道 DDR 模式 | P0 | Pending |

### 7.2 DSI 协议层
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| DSI-PRO-001 | 长包传输 | P0 | Pending |
| DSI-PRO-002 | 短包传输 | P0 | Pending |
| DSI-PRO-003 | DCS 命令支持 | P1 | Pending |
| DSI-PRO-004 | ECC 错误检测 | P1 | Pending |
| DSI-PRO-005 | CRC 校验 | P2 | Pending |

### 7.3 工作模式
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| DSI-MODE-001 | 视频模式（实时） | P0 | Pending |
| DSI-MODE-002 | 命令模式（异步） | P1 | Pending |
| DSI-MODE-003 | TE（Tearing Effect）同步 | P1 | Pending |

### 7.4 分辨率支持
| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| DSI-RES-001 | 3840×2160@60Hz (4 通道) | P0 | Pending |
| DSI-RES-002 | 2560×1440@120Hz (4 通道) | P1 | Pending |
| DSI-RES-003 | 1920×1080@144Hz (4 通道) | P1 | Pending |

---

## 8. 寄存器映射

### 8.1 控制寄存器
| Feature ID | 描述 | 偏移 | 验证状态 |
|------------|------|-------|----------|
| REG-CTRL-001 | DISPLAY_CTRL | 0x0000 | Pending |
| REG-CTRL-002 | DISPLAY_STATUS | 0x0004 | Pending |
| REG-CTRL-003 | 时序寄存器组 | 0x0008-0x0024 | Pending |
| REG-CTRL-004 | 帧缓冲寄存器组 | 0x0030-0x003C | Pending |

### 8.2 中断寄存器
| Feature ID | 描述 | 偏移 | 验证状态 |
|------------|------|-------|----------|
| REG-INT-001 | INT_STATUS | 0x0040 | Pending |
| REG-INT-002 | INT_MASK | 0x0044 | Pending |

### 8.3 色彩处理寄存器
| Feature ID | 描述 | 偏移 | 验证状态 |
|------------|------|-------|----------|
| REG-CLR-001 | COLOR_SPACE | 0x0100 | Pending |
| REG-CLR-002 | GAMMA_LUT_ADDR | 0x0104 | Pending |
| REG-CLR-003 | GAMMA_LUT_DATA | 0x0108 | Pending |

### 8.4 接口控制寄存器
| Feature ID | 描述 | 偏移 | 验证状态 |
|------------|------|-------|----------|
| REG-HDMI-001 | HDMI_CTRL | 0x0200 | Pending |
| REG-DP-001 | DP_CTRL | 0x0300 | Pending |
| REG-DSI-001 | DSI_CTRL | 0x0400 | Pending |

---

## 9. 功耗管理

| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| PWR-001 | 模块级时钟门控 | P0 | Pending |
| PWR-002 | 空闲状态自动降频 | P1 | Pending |
| PWR-003 | 未使用接口电源门控 | P1 | Pending |
| PWR-004 | DVFS 动态电压频率调节 | P2 | Pending |
| PWR-005 | 自适应刷新降低功耗 | P2 | Pending |

---

## 10. 功能安全

| Feature ID | 描述 | 优先级 | 验证状态 |
|------------|------|--------|----------|
| SAF-001 | CRC 校验覆盖关键数据 | P0 | Pending |
| SAF-002 | 看门狗定时器 | P1 | Pending |
| SAF-003 | 欠载错误检测 | P0 | Pending |
| SAF-004 | 双通道冗余比较 | P2 | Pending |

---

## 验证优先级定义

| 优先级 | 说明 |
|--------|------|
| P0 | 核心功能，必须验证通过 |
| P1 | 重要功能，建议验证通过 |
| P2 | 增强功能，按需验证 |
| P3 | 可选功能，资源允许时验证 |

---

## 文档版本历史

| 版本 | 日期 | 作者 | 变更说明 |
|------|------|------|----------|
| v1.0 | 2026-01-18 | YaoGuang Arch Team | 初始版本 |
