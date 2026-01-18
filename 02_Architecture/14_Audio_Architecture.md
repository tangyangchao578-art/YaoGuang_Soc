# 摇光(YaoGuang) Audio 模块架构规格

## 1. 概述

本文档定义了摇光车规级SoC芯片音频子系统的架构规格。音频模块负责车内音频信号的采集、处理与输出，支持多种音频接口协议，满足信息娱乐系统和ADAS系统的音频需求。

### 1.1 设计目标
- 支持多种音频接口：I2S、TDM、PDM、SPDIF
- 高保真音频处理能力，最高支持32-bit/384kHz
- 集成音频DSP，支持实时音效处理
- 低功耗设计，满足车规级能耗要求
- 功能安全支持，符合ASIL-B等级要求

### 1.2 参考标准
- Intel High Definition Audio Specification (Intel HD Audio)
- ARM SoundWire Specification
- MIPI Alliance SoundWire Serial Interface
- AES3 (AES/EBU) - SPDIF标准
- I2S Bus Specification (Philips Semiconductors)
- Pulse Density Modulation (PDM) Interfacing (MEMS Microphones)

---

## 2. 系统架构

### 2.1 顶层架构

```
┌─────────────────────────────────────────────────────────────────┐
│                        Audio Top Level                          │
├─────────────────────────────────────────────────────────────────┤
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐        │
│  │ I2S Ctrl │  │ TDM Ctrl │  │ PDM Ctrl │  │ SPDIF    │        │
│  │          │  │          │  │          │  │ Ctrl     │        │
│  └────┬─────┘  └────┬─────┘  └────┬─────┘  └─────┘        │
│       │            ┬──── │             │             │               │
│       └─────────────┴──────┬──────┴─────────────┘               │
│                            │                                    │
│                    ┌───────┴───────┐                            │
│                    │  Audio DSP    │                            │
│                    │  - SRC        │                            │
│                    │  - EQ         │                            │
│                    │  - DRC        │                            │
│                    │  - Mixer      │                            │
│                    └───────┬───────┘                            │
│                            │                                    │
│                    ┌───────┴───────┐                            │
│                    │ Volume Control│                            │
│                    └───────┬───────┘                            │
│                            │                                    │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                  APB Interface                           │   │
│  │              (Register Configuration)                    │   │
│  └─────────────────────────────────────────────────────────┘   │
│                            │                                    │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                  AXI-Stream Interface                    │   │
│  │              (Audio Data Streaming)                      │   │
│  └─────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────┘
```

### 2.2 接口信号定义

#### 2.2.1 系统接口
| 信号名 | 方向 | 位宽 | 描述 |
|--------|------|------|------|
| aclk | In | 1 | APB时钟 |
| aresetn | In | 1 | APB复位（低有效） |
| axi_aclk | In | 1 | AXI-Stream时钟 |
| axi_aresetn | In | 1 | AXI-Stream复位（低有效） |

#### 2.2.2 APB从接口
| 信号名 | 方向 | 位宽 | 描述 |
|--------|------|------|------|
| paddr | In | 12 | APB地址 |
| pwrite | In | 1 | 写使能 |
| pwdata | In | 32 | 写数据 |
| prdata | Out | 32 | 读数据 |
| psel | In | 1 | 选择信号 |
| penable | In | 1 | 使能信号 |
| pready | Out | 1 | 准备好信号 |

#### 2.2.3 AXI-Stream接口
| 信号名 | 方向 | 位宽 | 描述 |
|--------|------|------|------|
| tx_axis_tdata | Out | 64 | TX数据 |
| tx_axis_tvalid | Out | 1 | TX有效 |
| tx_axis_tready | In | 1 | TX就绪 |
| tx_axis_tkeep | Out | 8 | TX字节保持 |
| tx_axis_tlast | Out | 1 | TX最后 |
| rx_axis_tdata | In | 64 | RX数据 |
| rx_axis_tvalid | In | 1 | RX有效 |
| rx_axis_tready | Out | 1 | RX就绪 |
| rx_axis_tkeep | In | 8 | RX字节保持 |
| rx_axis_tlast | In | 1 | RX最后 |

---

## 3. 音频接口规格

### 3.1 I2S接口控制器

#### 3.1.1 特性
- 支持主模式和从模式
- 支持标准I2S、左对齐、右对齐格式
- 可配置数据位宽：16/20/24/32-bit
- 支持多通道音频（最多8通道）
- 可配置采样率：8kHz - 384kHz
- 支持字时钟（LRCLK）极性可配置
- 支持位时钟（BCLK）极性可配置

#### 3.1.2 接口信号
| 信号名 | 方向 | 描述 |
|--------|------|------|
| i2s_bclk | In/Out | 位时钟 |
| i2s_lrclk | In/Out | 左右声道时钟 |
| i2s_dout | Out | 数据输出 |
| i2s_din | In | 数据输入 |
| i2s_mclk | Out | 主时钟输出（可选） |

#### 3.1.3 时序参数
| 参数 | 最小值 | 典型值 | 最大值 | 单位 |
|------|--------|--------|--------|------|
| t_BCLK | - | 12.288 | - | MHz |
| t_SETUP | 10 | - | - | ns |
| t_HOLD | 5 | - | - | ns |
| t_VALID | - | - | 10 | ns |

### 3.2 TDM接口控制器

#### 3.2.1 特性
- 支持TDM128、TDM64、TDM32、TDM16帧格式
- 可配置时隙数：2 - 32
- 可配置每时隙位宽：8/16/24/32-bit
- 支持多芯片级联
- 支持帧同步脉冲极性配置
- 支持位时钟极性配置

#### 3.2.2 TDM帧格式
```
TDM128 Frame (8 channels × 16-bit):
┌──────┬──────┬──────┬──────┬──────┬──────┬──────┬──────┐
│ Ch0  │ Ch1  │ Ch2  │ Ch3  │ Ch4  │ Ch5  │ Ch6  │ Ch7  │
│ 16b  │ 16b  │ 16b  │ 16b  │ 16b  │ 16b  │ 16b  │ 16b  │
└──────┴──────┴──────┴──────┴──────┴──────┴──────┴──────┘
←──────────────────── 128 BCLK cycles ──────────────────→

FS (Frame Sync) pulses at the beginning of each frame
```

### 3.3 PDM接口控制器

#### 3.3.1 特性
- 支持MEMS麦克风接口
- 可配置过采样率：64x/128x/256x
- 内置PDM到PCM转换器
- 支持双麦克风立体声输入
- 可配置高通滤波器（去直流偏移）
- 可配置低通滤波器（抗混叠）

#### 3.3.2 PDM规格
| 参数 | 值 |
|------|------|
| 输入格式 | 1-bit PDM |
| 采样率 | 48kHz / 96kHz / 192kHz |
| 有效位数 | 16-bit / 24-bit (after decimation) |
| 通道数 | 2 (stereo) / 4 (quad) |

### 3.4 SPDIF接口控制器

#### 3.4.1 特性
- 符合AES3/IEC60958标准
- 支持线性PCM和非压缩音频
- 支持用户数据位（UCD）传输
- 内置抖动抑制电路
- 可配置输出电平
- 支持源/汇模式

#### 3.4.2 电气规格
| 参数 | 值 |
|------|------|
| 编码方式 | Biphase Mark Code (BMC) |
| 传输速率 | 3.072 Mbps (64×48kHz) |
| 阻抗 | 75Ω (coax) / 110Ω (optical) |
| 输出电幅 | 0.5Vpp - 1.0Vpp |

---

## 4. 音频处理能力

### 4.1 采样率支持

| 采样率 | 用途 | 精度 |
|--------|------|------|
| 8 kHz | 语音采集 | ±0.1% |
| 16 kHz | 语音识别 | ±0.1% |
| 22.05 kHz | 音频播放 | ±0.1% |
| 44.1 kHz | CD质量 | ±0.01% |
| 48 kHz | 专业音频 | ±0.01% |
| 96 kHz | Hi-Res音频 | ±0.01% |
| 192 kHz | Hi-Res音频 | ±0.01% |
| 384 kHz | 专业母带 | ±0.01% |

### 4.2 位深度支持

| 位深度 | 动态范围 | THD+N |
|--------|----------|-------|
| 16-bit | 96 dB | < -90 dB |
| 20-bit | 120 dB | < -100 dB |
| 24-bit | 144 dB | < -110 dB |
| 32-bit float | 144+ dB | < -110 dB |

### 4.3 通道配置

| 模式 | 最大通道数 | 用途 |
|------|------------|------|
| 立体声 | 2 | 耳机输出 |
| 环绕声 | 6 | 车内环绕音响 |
| 多声道 | 8 | 音频处理 |
| PDM阵列 | 16 | 麦克风阵列 |

---

## 5. 音频DSP规格

### 5.1 DSP架构

```
┌─────────────────────────────────────────────────────────────┐
│                      Audio DSP Core                         │
├─────────────────────────────────────────────────────────────┤
│  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐        │
│  │   MAC   │  │   MAC   │  │   MAC   │  │   MAC   │        │
│  │ Unit 0  │  │ Unit 1  │  │ Unit 2  │  │ Unit 3  │        │
│  └─────────┘  └─────────┘  └─────────┘  └─────────┘        │
│                        ↓                                    │
│  ┌─────────────────────────────────────────────────────┐   │
│  │              32×32-bit Register File                 │   │
│  └─────────────────────────────────────────────────────┘   │
│                        ↓                                    │
│  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐        │
│  │  ALU    │  │ Shifter │  │  Acc    │  │  cmp    │        │
│  └─────────┘  └─────────┘  └─────────┘  └─────────┘        │
│                        ↓                                    │
│  ┌─────────────────────────────────────────────────────┐   │
│  │              Instruction Cache (4KB)                  │   │
│  └─────────────────────────────────────────────────────┘   │
│                        ↓                                    │
│  ┌─────────────────────────────────────────────────────┐   │
│  │ (16KB)              Data Memory                       │   │
│  └─────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────┘
```

### 5.2 DSP性能指标

| 参数 | 值 |
|------|------|
| 处理器类型 | Harvard架构 |
| 乘法累加器 | 4个并行MAC |
| 时钟频率 | 200 MHz |
| 峰值性能 | 1.6 GMAC/s |
| 指令缓存 | 4KB |
| 数据缓存 | 16KB |
| 位宽 | 32-bit fixed point / 32-bit float |

### 5.3 DSP功能模块

#### 5.3.1 采样率转换器 (SRC)
- 支持异步采样率转换
- 输入范围：8kHz - 384kHz
- 输出范围：8kHz - 384kHz
- 转换质量：140dB SNR
- 算法：多相插值滤波器

#### 5.3.2 均衡器 (EQ)
- 支持10段参数均衡
- 滤波器类型：Peak/Notch, Low-Shelf, High-Shelf, All-Pass
- 每段可配置：频率、增益、Q值
- 精度：24-bit

#### 5.3.3 动态范围压缩器 (DRC)
- 阈值可配置：-60dBFS 到 0dBFS
- 压缩比：1:1 到 ∞:1
- 启动时间：0.1ms - 100ms
- 释放时间：10ms - 1000ms
- 硬/软拐点可选

#### 5.3.4 混音器 (Mixer)
- 最大输入通道：16
- 输出通道：2
- 每通道独立增益控制
- 静音功能
- 溢出保护

#### 5.3.5 3D音效处理
- 虚拟环绕声
- 声场扩展
- 频率扩展

---

## 6. 音量控制

### 6.1 功能规格

| 功能 | 描述 |
|------|------|
| 音量范围 | -100dB 到 +12dB |
| 步进精度 | 0.5dB |
| 通道独立控制 | 每个通道独立 |
| 静音 | 硬件静音 (< -100dB) |
| 削波保护 | 自动限幅器 |
| 渐变时间 | 0 - 1000ms 可配置 |

### 6.2 音量曲线

```verilog
// 音量控制公式
volume_db = volume_reg * 0.5;  // 0.5dB步进

// 线性增益计算
gain_linear = 10^(volume_db / 20);

// 数字音量实现
output_sample = input_sample * gain_linear >> volume_shift;
```

---

## 7. 功耗预算

### 7.1 功耗分析

| 模块 | 动态功耗 | 静态功耗 | 总功耗 |
|------|----------|----------|--------|
| I2S Controller | 5 mW | 1 mW | 6 mW |
| TDM Controller | 8 mW | 1 mW | 9 mW |
| PDM Controller | 3 mW | 0.5 mW | 3.5 mW |
| SPDIF Controller | 4 mW | 0.5 mW | 4.5 mW |
| Audio DSP | 45 mW | 5 mW | 50 mW |
| Volume Control | 1 mW | 0.2 mW | 1.2 mW |
| SRC | 8 mW | 1 mW | 9 mW |
| 总计 | 74 mW | 9.2 mW | 83.2 mW |

### 7.2 低功耗模式

| 模式 | 功耗 | 唤醒时间 | 说明 |
|------|------|----------|------|
| Active | 83 mW | 0 | 全速运行 |
| Idle | 10 mW | 10μs | 时钟门控 |
| Standby | 2 mW | 100μs | 仅保留寄存器 |
| Power Down | 0.1 mW | 1ms | 电源门控 |

### 7.3 功耗管理策略

- 时钟门控：空闲模块自动门控时钟
- 电源门控：独立电源域控制
- 动态电压频率调节（DVFS）：根据负载调整
- 局部关断：单个音频通道可独立关闭

---

## 8. 寄存器映射

### 8.1 寄存器地址映射

| 地址偏移 | 名称 | 访问 | 描述 |
|----------|------|------|------|
| 0x0000 | AUDIO_CTRL | RW | 全局控制寄存器 |
| 0x0004 | AUDIO_STAT | RO | 状态寄存器 |
| 0x0008 | AUDIO_INT_EN | RW | 中断使能 |
| 0x000C | AUDIO_INT_STAT | RO/W1C | 中断状态 |
| 0x0010 | I2S_CTRL | RW | I2S控制 |
| 0x0014 | I2S_STAT | RO | I2S状态 |
| 0x0018 | TDM_CTRL | RW | TDM控制 |
| 0x001C | TDM_STAT | RO | TDM状态 |
| 0x0020 | PDM_CTRL | RW | PDM控制 |
| 0x0024 | PDM_STAT | RO | PDM状态 |
| 0x0028 | SPDIF_CTRL | RW | SPDIF控制 |
| 0x002C | SPDIF_STAT | RO | SPDIF状态 |
| 0x0030 | VOL_MASTER | RW | 主音量 |
| 0x0034 | VOL_CH0 | RW | 通道0音量 |
| 0x0038 | VOL_CH1 | RW | 通道1音量 |
| 0x0040 | SRC_CTRL | RW | 采样率转换控制 |
| 0x0044 | SRC_RATIO | RW | 采样率比率 |
| 0x0050 | EQ_CTRL | RW | 均衡器控制 |
| 0x0054 | EQ_BAND0 | RW | EQ频段0 |
| 0x0058 | EQ_BAND1 | RW | EQ频段1 |
| 0x005C | EQ_BAND2 | RW | EQ频段2 |
| 0x0100 | DSP_CTRL | RW | DSP控制 |
| 0x0104 | DSP_STAT | RO | DSP状态 |
| 0x1000 | DSP_IRAM0 | RW | DSP指令RAM |
| 0x2000 | DSP_DRAM0 | RW | DSP数据RAM |

---

## 9. 功能安全

### 9.1 安全目标

| 安全目标 | ASIL等级 | 描述 |
|----------|----------|------|
| 音频输出失效检测 | ASIL-B | 检测音频输出错误 |
| 配置寄存器保护 | ASIL-B | 防止非法寄存器访问 |
| 状态监控 | ASIL-B | 实时监控系统状态 |

### 9.2 安全机制

#### 9.2.1 看门狗定时器
- 监控DSP程序执行
- 超时时间：100ms - 1s可配置
- 自动复位DSP

#### 9.2.2 寄存器冗余存储
- 关键寄存器双份存储
- 周期比较检测
- 不一致时触发中断

#### 9.2.3 ECC保护
- DSP指令RAM：SEC-DED ECC
- DSP数据RAM：SEC-DED ECC
- 音频数据通路：奇偶校验

#### 9.2.4 音频环路检测
- DAC输出环回ADC输入检测
- 持续监控音频通路完整性
- 检测到故障时触发安全中断

### 9.3 故障模式与响应

| 故障模式 | 检测机制 | 响应措施 |
|----------|----------|----------|
| DSP死机 | 看门狗 | 系统复位 |
| 寄存器翻转 | 冗余比较 | 中断+恢复 |
| RAM单比特错误 | ECC纠正 | 继续运行+记录 |
| RAM多比特错误 | ECC检测 | 安全中断 |
| 音频数据错误 | 奇偶校验 | 静音+中断 |
| 时钟故障 | 时钟监控器 | 切换备用时钟 |

---

## 10. 时钟与复位

### 10.1 时钟架构

| 时钟域 | 源 | 频率 | 用途 |
|--------|------|------|------|
| apb_clk | CLK_APB | 100 MHz | APB配置接口 |
| audio_clk | PLL_AUDIO | 200 MHz | 音频DSP |
| i2s_clk | AUDIO_DIV | 12.288 MHz | I2S BCLK |
| tdm_clk | AUDIO_DIV | 24.576 MHz | TDM BCLK |
| spdif_clk | AUDIO_DIV | 24.576 MHz | SPDIF时钟 |

### 10.2 复位架构

| 复位域 | 源 | 极性 | 描述 |
|--------|------|------|------|
| aresetn | POR | 低有效 | APB复位 |
| axi_aresetn | POR | 低有效 | AXI-Stream复位 |
| audio_rst_n | RSTMGR | 低有效 | 音频域复位 |
| dsp_rst_n | RSTMGR | 低有效 | DSP复位 |

---

## 11. 验证计划

### 11.1 模块级验证

| 测试项 | 验证方法 | 覆盖率目标 |
|--------|----------|------------|
| I2S时序 | 仿真 | 100% |
| TDM帧格式 | 仿真 | 100% |
| PDM转PCM | 仿真 | 100% |
| SPDIF编解码 | 仿真 | 100% |
| DSP指令集 | 仿真 | 100% |
| SRC算法 | 仿真 | 100% |
| 音量控制 | 仿真 | 100% |

### 11.2 系统级验证

| 测试项 | 验证方法 |
|--------|----------|
| 多协议同时工作 | 仿真+Emulation |
| 功耗测量 | FPGA |
| 启动时序 | FPGA |
| 中断响应 | 仿真 |
| 功能安全机制 | 故障注入 |

---

## 12. 版本历史

| 版本 | 日期 | 作者 | 描述 |
|------|------|------|------|
| 1.0 | 2026-01-18 | 架构组 | 初始版本 |

---

## 附录

### A. 缩略语

| 缩略语 | 全称 |
|--------|------|
| I2S | Inter-IC Sound |
| TDM | Time Division Multiplexing |
| PDM | Pulse Density Modulation |
| SPDIF | Sony/Philips Digital Interface Format |
| DSP | Digital Signal Processor |
| SRC | Sample Rate Converter |
| EQ | Equalizer |
| DRC | Dynamic Range Compression |
| MAC | Multiply-Accumulate |
| ECC | Error Correcting Code |
| BCLK | Bit Clock |
| LRCLK | Left/Right Clock |
| MCLK | Master Clock |
| BMC | Biphase Mark Code |
| THD+N | Total Harmonic Distortion + Noise |
| SNR | Signal-to-Noise Ratio |

### B. 参考文献

1. Intel High Definition Audio Specification, Revision 1.0a
2. MIPI Alliance SoundWire Specification, Version 1.0
3. AES3-2009 (r2020): Audio Equipment Digital Audio Interface
4. I2S Bus Specification, Philips Semiconductors, 1986
5. IEC 60958: Digital Audio Interface
