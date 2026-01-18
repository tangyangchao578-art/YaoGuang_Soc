# 摇光(YaoGuang) SoC 安全机制手册 (Safety Manual)

> **文档版本**: V1.0  
> **编制日期**: 2026-01-18  
> **状态**: 初稿  
> **适用标准**: ISO 26262:2018  
> **安全等级**: ASIL-D

---

## 1. 概述

### 1.1 目的

本文档描述摇光SoC中实现的所有**硬件安全机制**，用于满足ASIL-D安全要求。

### 1.2 安全机制概览

| 机制类型 | 数量 | 覆盖模块 | DC目标 |
|----------|------|----------|--------|
| 锁步冗余 | 1 | Safety Island | 99% |
| ECC保护 | 6 | 存储系统 | 99.9% |
| 看门狗 | 2 | 全系统 | 99% |
| 电压监控 | 4 | 电源系统 | 95% |
| 时钟监控 | 3 | 时钟系统 | 95% |
| 温度监控 | 2 | 热管理 | 90% |
| BIST | 2 | 存储/逻辑 | 95% |

---

## 2. Safety Island

### 2.1 架构

```
┌──────────────────────────────────────────────────────────────┐
│                      Safety Island                           │
├──────────────────────────────────────────────────────────────┤
│  ┌─────────────┐  ┌─────────────┐                            │
│  │  Cortex-R52 │  │  Cortex-R52 │  双核锁步                  │
│  │    Core 0   │  │    Core 1   │                            │
│  └──────┬──────┘  └──────┬──────┘                            │
│         │                │                                    │
│         └───────┬────────┘                                    │
│                 ▼                                             │
│         ┌──────────────┐                                     │
│         │   比较器     │   检测核间不匹配                      │
│         └──────┬───────┘                                     │
│                │                                              │
│    ┌───────────┼───────────┐                                 │
│    ▼           ▼           ▼                                 │
│ ┌──────┐  ┌───────┐  ┌───────┐                               │
│ │WDT   │  │ PMU   │  │ Fault │                               │
│ │看门狗│  │监控   │  │控制   │                               │
│ └──────┘  └───────┘  └───────┘                               │
└──────────────────────────────────────────────────────────────┘
```

### 2.2 锁步比较器

```verilog
module lockstep_comparator (
  input  wire [31:0] result0,
  input  wire [31:0] result1,
  input  wire        valid,
  output reg         mismatch,
  output reg [31:0]  error_mask
);
  always @(posedge clk) begin
    if (valid) begin
      mismatch <= (result0 != result1);
      error_mask <= result0 ^ result1;
      if (mismatch) begin
        // 触发安全响应
        fault_controller.trigger(FAULT_LOCKSTEP_MISMATCH);
      end
    end
  end
endmodule
```

### 2.3 窗口看门狗

```verilog
module window_watchdog (
  input  wire clk,
  input  wire rst_n,
  input  wire kick,
  input  wire [31:0] window_min,   // 最小刷新窗口
  input  wire [31:0] window_max,   // 最大刷新窗口
  output reg  timeout
);
  reg [31:0] counter;
  
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      counter <= 0;
      timeout <= 0;
    end else begin
      counter <= counter + 1;
      if (counter > window_max) begin
        timeout <= 1;
        fault_controller.trigger(FAULT_WDT_TIMEOUT);
      end
      if (kick) begin
        if (counter < window_min) begin
          // 刷新太早，虚假触发
          fault_controller.trigger(FAULT_WDT_EARLY_KICK);
        end
        counter <= 0;
        timeout <= 0;
      end
    end
  end
endmodule
```

### 2.4 安全响应机制

| 事件 | 响应 | FTTI |
|------|------|------|
| 锁步不匹配 | 系统复位 | 5ms |
| 看门狗超时 | 系统复位 | 10ms |
| 电压异常 | 降频/复位 | 10ms |
| 温度超限 | 降频/关断 | 50ms |

---

## 3. ECC保护

### 3.1 ECC配置

| 存储类型 | ECC类型 | 检测能力 | 纠正能力 |
|----------|---------|---------|---------|
| L1 Cache | SECDED (32,7) | 2位 | 1位 |
| L2 Cache | SECDED (64,8) | 2位 | 1位 |
| L3 Cache | SECDED (64,8) | 2位 | 1位 |
| Register File | SECDED (32,7) | 2位 | 1位 |
| 本地SRAM | SECDED (64,8) | 2位 | 1位 |

### 3.2 ECC编码器

```verilog
module ecc_encoder (
  input  [31:0] data_in,
  output [38:0] data_out  // 32位数据 + 7位校验
);
  // 生成32位数据的SECDED码
  assign {data_out[31:0], data_out[38:32]} = 
    encode_secded(data_in);
endmodule
```

### 3.3 ECC解码器

```verilog
module ecc_decoder (
  input  [38:0] data_in,
  output [31:0] data_out,
  output [1:0]  error_type,     // 00:无错误, 01:单位错误, 10:双位错误
  output        error_interrupt
);
  wire [31:0] corrected_data;
  wire [6:0] syndrome;
  
  // 解码并纠正
  decode_secded u_dec (.data_in(data_in), 
                       .data_out(corrected_data),
                       .syndrome(syndrome));
  
  assign error_type = (syndrome == 0) ? 2'b00 :
                      (|syndrome[6:1]) ? 2'b10 : 2'b01;
  
  assign data_out = (error_type == 2'b01) ? corrected_data : data_in;
  assign error_interrupt = (error_type != 2'b00);
endmodule
```

---

## 4. 电压监控

### 4.1 电压监控器配置

| 监控点 | 阈值(典型值) | 响应 |
|--------|-------------|------|
| VDD_CORE (0.75V) | 0.675V / 0.825V | 欠压复位 / 过压告警 |
| VDD_NPU (0.8V) | 0.72V / 0.88V | 欠压复位 / 过压告警 |
| VDD_IO (1.8V) | 1.62V / 1.98V | 欠压告警 / 过压告警 |
| VDD_SAFETY (0.8V) | 0.72V / 0.88V | 欠压复位 / 过压告警 |

### 4.2 电压监控实现

```verilog
module voltage_monitor (
  input  wire          clk,
  input  wire          rst_n,
  input  wire [11:0]   vdd_sample,    // ADC采样值
  input  wire [11:0]   vdd_under_th,  // 欠压阈值
  input  wire [11:0]   vdd_over_th,   // 过压阈值
  output reg           under_voltage,
  output reg           over_voltage
);
  always @(posedge clk) begin
    under_voltage <= (vdd_sample < vdd_under_th);
    over_voltage  <= (vdd_sample > vdd_over_th);
    if (under_voltage) begin
      fault_controller.trigger(FAULT_UNDER_VOLTAGE);
    end
  end
endmodule
```

---

## 5. 时钟监控

### 5.1 时钟监控配置

| 时钟域 | 监控目标 | 检测机制 |
|--------|---------|----------|
| clk_core | 2.0 GHz ± 10% | 频率计数器 |
| clk_safety | 200 MHz ± 5% | 与RTC比较 |
| clk_rtc | 32.768 kHz ± 1% | 独立验证 |

### 5.2 时钟监控实现

```verilog
module clock_monitor (
  input  wire clk_mon,      // 被监控时钟
  input  wire clk_ref,      // 参考时钟
  input  wire rst_n,
  output reg  clk_error
);
  reg [31:0] ref_count;
  reg [31:0] mon_count;
  
  always @(posedge clk_ref) begin
    mon_count <= 0;
    ref_count <= ref_count + 1;
  end
  
  always @(posedge clk_mon) begin
    mon_count <= mon_count + 1;
  end
  
  // 检查mon_count是否在预期范围内
  wire [31:0] expected = ref_count * (clk_mon_freq / clk_ref_freq);
  wire [31:0] tolerance = expected / 10;  // 10% 容差
  
  always @(posedge clk_ref) begin
    if (mon_count < expected - tolerance || 
        mon_count > expected + tolerance) begin
      clk_error <= 1;
      fault_controller.trigger(FAULT_CLOCK_ERROR);
    end else begin
      clk_error <= 0;
    end
  end
endmodule
```

---

## 6. 温度监控

### 6.1 温度监控配置

| 监控点 | 警告阈值 | 危险阈值 | 响应 |
|--------|---------|---------|------|
| Die温度 | 100°C | 125°C | 降频 / 关断 |
| NPU温度 | 90°C | 110°C | 降频 / 关断 |

### 6.2 温度响应策略

```
温度 < 90°C:      正常运行
90°C < T < 100°C: 警告，降频10%
100°C < T < 110°C: 严重警告，降频30%
T > 110°C:         关断NPU
T > 125°C:         系统复位
```

---

## 7. BIST机制

### 7.1 MBIST配置

| 测试对象 | 测试算法 | 执行时机 |
|----------|---------|----------|
| L1 Cache | March C- | 上电自检 |
| L2 Cache | March C- | 上电自检 + 定期 |
| L3 Cache | March A | 上电自检 |
| Register File | Checkerboard | 上电自检 |

### 7.2 LBIST配置

| 参数 | 值 |
|------|-----|
| 模式 | STUMPS架构 |
| 压缩比 | 100:1 |
| 测试向量数 | 10,000 |
| 目标覆盖率 | 95% |

---

## 8. 安全机制覆盖矩阵

| 安全机制 | SG-01 | SG-02 | SG-03 | SG-04 |
|----------|-------|-------|-------|-------|
| Safety Island锁步 | ● | ● | ● | ● |
| NPU ECC | ● | | | |
| NPU结果校验 | ● | | | |
| CPU ECC | | ● | | |
| CPU锁步校验 | | ● | | |
| 存储 ECC | ● | ● | ● | |
| 窗口看门狗 | | ● | ● | ● |
| 电压监控 | | | ● | ● |
| 时钟监控 | | | | ● |
| 温度监控 | | | | ● |
| MBIST | ● | ● | ● | ● |
| LBIST | ● | ● | ● | ● |

---

## 9. 验证要求

| 安全机制 | 验证方法 | 目标DC |
|----------|---------|--------|
| 锁步比较 | 故障注入 | 99% |
| ECC | 故障注入 | 99.9% |
| 看门狗 | 故障注入 | 99% |
| 电压监控 | 边界测试 | 95% |
| 时钟监控 | 故障注入 | 95% |
| MBIST | ATPG | 99% |
| LBIST | ATPG | 95% |

---

## 审批

| 角色 | 姓名 | 签名 | 日期 |
|------|------|------|------|
| 编制 | 功能安全专家 | | 2026-01-18 |
| 审核 | | | |
| 批准 | | | |

---

**文档版本**: V1.0  
**最后更新**: 2026-01-18  
**状态**: 初稿
