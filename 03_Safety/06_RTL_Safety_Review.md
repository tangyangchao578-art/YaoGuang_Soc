# 摇光(YaoGuang) SoC RTL安全审查报告

> **文档版本**: V1.0  
> **审查日期**: 2026-01-18  
> **审查人**: 功能安全专家 (FuSa)  
> **适用标准**: ISO 26262:2018  
> **目标安全等级**: ASIL-D

---

## 文档信息

| 项目 | 内容 |
|------|------|
| 文档编号 | YG-FUSA-RTL-REVIEW-001 |
| 项目名称 | 摇光自动驾驶SoC |
| 审查范围 | Safety Island RTL代码 |
| 安全等级目标 | ASIL-D |
| 审查人 | 功能安全专家 |
| 审核人 | 待定 |
| 批准人 | 待定 |

---

## 修订历史

| 版本 | 日期 | 修订人 | 修订内容 |
|------|------|--------|----------|
| V1.0 | 2026-01-18 | FuSa | 初稿 |

---

## 目录

1. [审查概述](#1-审查概述)
2. [审查方法论](#2-审查方法论)
3. [模块级审查](#3-模块级审查)
4. [发现问题汇总](#4-发现问题汇总)
5. [RTL修改建议](#5-rtl修改建议)
6. [后续行动](#6-后续行动)

---

## 1. 审查概述

### 1.1 审查范围

本次RTL安全审查覆盖以下Safety Island关键模块：

| 文件 | 功能 | ASIL等级 |
|------|------|----------|
| `cortex_r52_lockstep.sv` | 双核锁步比较器 | ASIL D+ |
| `safety_watchdog.sv` | 安全看门狗 | ASIL D |
| `ecc_memory_controller.sv` | ECC内存控制器 | ASIL D |
| `safety_island_top.sv` | Safety Island顶层 | ASIL D+ |
| `power_monitor.sv` | 电源监控器 | ASIL C |
| `safe_clock_reset.sv` | 时钟复位管理 | ASIL D |

### 1.2 审查标准

| 标准 | 要求 |
|------|------|
| ISO 26262 Part 5 | 硬件层面产品开发 |
| ISO 26262 Part 9 | ASIL分解和安全分析 |
| 诊断覆盖率 | ASIL D ≥ 99% |
| SPFM | ASIL D ≥ 99% |
| PMHF | ASIL D < 10 FIT |

### 1.3 总体评价

| 评价维度 | 评级 | 说明 |
|----------|------|------|
| 架构完整性 | ⚠️ 需改进 | Safety Island采用双模锁步，需评估是否满足ASIL D+ |
| 安全机制覆盖 | ⚠️ 需改进 | 部分安全机制缺少自检和冗余 |
| RTL编码质量 | ✅ 基本符合 | 编码规范良好，需增强安全相关逻辑 |
| 错误响应 | ⚠️ 需改进 | 错误响应路径不够直接 |
| 可测试性 | ⚠️ 需改进 | BIST覆盖率不足 |

---

## 2. 审查方法论

### 2.1 审查维度

| 维度 | 检查项 |
|------|--------|
| **功能正确性** | 安全机制功能是否正确实现 |
| **冗余设计** | 是否有足够的冗余和独立性 |
| **错误覆盖** | 是否覆盖所有失效模式 |
| **诊断能力** | 故障检测能力是否达标 |
| **响应机制** | 错误响应是否及时有效 |
| **自检能力** | 安全机制是否能自检 |
| **编码规范** | 是否符合安全编码标准 |

### 2.2 失效模式覆盖检查清单

| 失效模式 | 检查方法 |
|----------|----------|
| 固定0/1故障 | 代码逻辑分析 |
| 桥接故障 | 结构分析 |
| 单粒子翻转(SEU) | 冗余和ECC检查 |
| 亚稳态 | 时钟复位同步分析 |
| 共因失效 | 独立性分析 |
| 延迟故障 | 时序分析 |

---

## 3. 模块级审查

### 3.1 cortex_r52_lockstep.sv - 双核锁步比较器

#### 3.1.1 代码概述

| 项目 | 内容 |
|------|------|
| 功能 | Cortex-R52双核锁步比较 |
| 架构 | 主核(Core0) + 影子核(Core1, 延迟1周期) |
| 关键信号 | lockstep_error, error_code |

#### 3.1.2 优势

| 序号 | 优势 | 说明 |
|------|------|------|
| ✅ 1 | 完整的AXI接口保护 | 覆盖AR/AW/R/B通道 |
| ✅ 2 | 详细的错误码 | 区分地址/数据/响应错误 |
| ✅ 3 | 1周期延迟对齐 | 确保时序同步比较 |
| ✅ 4 | 错误代码详细记录 | 包含错误位置信息 |

#### 3.1.3 发现的问题

| 问题ID | 问题描述 | 严重度 | ASIL影响 |
|--------|----------|--------|----------|
| **RTL-LS-001** | 比较器无自检机制 | 高 | D+ |
| **RTL-LS-002** | 双核共享相同时钟域 | 高 | D+ |
| **RTL-LS-003** | 错误输出为寄存器,非组合逻辑 | 中 | D |
| **RTL-LS-004** | 缺少直接复位触发路径 | 中 | D |

##### 问题RTL-LS-001: 比较器无自检

**位置**: `cortex_r52_lockstep.sv:216-223`

**问题代码**:
```verilog
always_comb begin
    ar_mismatch     = core1_arvalid_d && (core0_araddr != core1_araddr_d);
    rdata_mismatch  = core1_rvalid_d && (core0_rdata != core1_rdata_d);
    rresp_mismatch  = core1_rvalid_d && (core0_rresp != core1_rresp_d);
    rvalid_mismatch = core0_rvalid != core1_rvalid_d;
    compare_error = ar_mismatch || rdata_mismatch || rresp_mismatch || rvalid_mismatch;
end
```

**风险分析**:
- 比较器逻辑本身可能出现固定故障
- 如果比较器卡住0,所有比较结果将始终为"相等"
- 如果比较器卡住1,所有比较结果将始终为"不相等"
- 当前设计无法检测这类故障

**ISO 26262要求**: ASIL D要求99%诊断覆盖率,缺少自检无法满足

##### 问题RTL-LS-002: 双核共享相同时钟域

**位置**: `cortex_r52_lockstep.sv:97-131, 164-199`

**问题分析**:
```verilog
cortex_r52_core u_core0 (
    .clk_i                 (clk_i),  // 同一时钟
    ...
);

cortex_r52_core u_core1 (
    .clk_i                 (clk_i),  // 同一时钟
    ...
);
```

**共因失效场景**:
- PLL故障导致时钟停止 → 双核同时停止
- 时钟分配网络故障 → 双核同时失效
- 电源噪声 → 双核同时出错

**风险等级**: ASIL D+要求共因失效率<0.1 FIT,当前设计存在高风险

##### 问题RTL-LS-003: 错误输出为寄存器路径

**位置**: `cortex_r52_lockstep.sv:228-248`

**问题代码**:
```verilog
always_ff @(posedge clk_i or negedge rst_n_i) begin
    if (!rst_n_i) begin
        error_o <= '0;
        error_code_o <= '0;
    end else begin
        error_o <= compare_error;  // 寄存器输出
        ...
    end
end
```

**影响**: 错误检测延迟1个时钟周期,在200MHz时钟下为5ns延迟

**建议**: 添加组合逻辑错误输出作为冗余路径

##### 问题RTL-LS-004: 缺少直接复位触发

**问题分析**: 锁步错误仅设置error_o信号,未直接触发系统复位

**当前流程**:
```
锁步错误 → error_o = 1 → 上报 → 软件处理 → 复位
```

**建议流程**:
```
锁步错误 → error_o = 1 → 直接触发硬件复位 + 错误上报
```

#### 3.1.4 RTL修改建议

```verilog
// 建议1: 添加比较器自检逻辑
logic compare_test_mode;
logic compare_stuck_at_0, compare_stuck_at_1;

always @(posedge clk_i or negedge rst_n_i) begin
    if (!rst_n_i) begin
        compare_test_mode <= 1'b0;
        compare_stuck_at_0 <= 1'b0;
        compare_stuck_at_1 <= 1'b0;
    end else if (test_mode_enable_i) begin
        compare_test_mode <= 1'b1;
        // 注入测试向量
        compare_stuck_at_0 <= test_inject_0;
        compare_stuck_at_1 <= test_inject_1;
    end
end

// 组合逻辑错误输出(立即响应)
assign error_comb_o = compare_error;

// 自检时验证比较器功能
assign compare_test_result = (compare_stuck_at_0 && compare_error) || 
                            (compare_stuck_at_1 && !compare_error);
```

---

### 3.2 safety_watchdog.sv - 安全看门狗

#### 3.2.1 代码概述

| 项目 | 内容 |
|------|------|
| 功能 | 窗口看门狗,带外部接口 |
| 模式 | 简单模式 + 窗口模式 |
| 外部接口 | 脉冲输出,反馈输入 |

#### 3.2.2 优势

| 序号 | 优势 | 说明 |
|------|------|------|
| ✅ 1 | 窗口模式支持 | 防止虚假喂狗 |
| ✅ 2 | 外部看门狗接口 | 支持系统级看门狗级联 |
| ✅ 3 | 早期警告 | 提前100个周期预警 |
| ✅ 4 | 错误聚合 | 接收lockstep/ecc错误 |

#### 3.2.3 发现的问题

| 问题ID | 问题描述 | 严重度 | ASIL影响 |
|--------|----------|--------|----------|
| **RTL-WDT-001** | 窗口检测使用混合赋值 | 高 | D |
| **RTL-WDT-002** | 看门狗可被禁用 | 高 | D |
| **RTL-WDT-003** | 缺少独立时钟监控 | 中 | D |
| **RTL-WDT-004** | 超时未直接输出复位 | 中 | D |

##### 问题RTL-WDT-001: 混合赋值问题

**位置**: `safety_watchdog.sv:105-107`

**问题代码**:
```verilog
always_ff @(posedge clk_i or negedge rst_n_i) begin
    if (!rst_n_i) begin
        in_window <= 1'b0;
    end else begin
        in_window = (counter >= window_open) && (counter < window_close);  // 混合赋值!
    end
end
```

**风险**:
- `always_ff`块中使用`=`赋值是仿真与综合不一致的根源
- 可能导致综合后功能与仿真不符
- 违反编码规范

##### 问题RTL-WDT-002: 看门狗可禁用

**位置**: `safety_watchdog.sv:91-96`

**问题代码**:
```verilog
always_ff @(posedge clk_i or negedge rst_n_i) begin
    if (!rst_n_i) begin
        watchdog_enable <= 1'b1;
        ...
    end else begin
        watchdog_enable <= cfg_enable_i;  // 可配置禁用!
    end
end
```

**风险**: 软件可能意外禁用看门狗,导致系统失去保护

##### 问题RTL-WDT-004: 超时未直接复位

**当前实现**: 超时仅设置`timeout_o`和`error_o`信号

**建议**: 添加直接复位触发信号
```verilog
assign reset_request_o = timeout_o || error_o || lockstep_error_i || ecc_error_i;
```

#### 3.2.4 RTL修改建议

```verilog
// 建议1: 修正混合赋值
always_ff @(posedge clk_i or negedge rst_n_i) begin
    if (!rst_n_i) begin
        in_window <= 1'b0;
    end else begin
        in_window <= (counter >= window_open) && (counter < window_close);
    end
end

// 建议2: 看门狗使能应为只读或硬件固定
// 移除cfg_enable_i输入,或添加硬件看门狗使能锁

// 建议3: 添加直接复位输出
assign reset_request_o = timeout_o | error_o | lockstep_error_i | ecc_error_i;
```

---

### 3.3 ecc_memory_controller.sv - ECC内存控制器

#### 3.3.1 代码概述

| 项目 | 内容 |
|------|------|
| 功能 | 64位数据SECDED保护 |
| ECC类型 | Hamming SECDED (8位校验) |
| BIST | 支持MBIST |

#### 3.3.2 优势

| 序号 | 优势 | 说明 |
|------|------|------|
| ✅ 1 | SECDED实现 | 支持单错纠正,双错检测 |
| ✅ 2 | 错误码详细 | 区分单错/双错,包含地址信息 |
| ✅ 3 | MBIST接口 | 支持内置自测试 |
| ✅ 4 | AXI接口 | 完整的AXI从接口 |

#### 3.3.3 发现的问题

| 问题ID | 问题描述 | 严重度 | ASIL影响 |
|--------|----------|--------|----------|
| **RTL-ECC-001** | ECC编码算法过于简化 | 高 | D |
| **RTL-ECC-002** | BIST覆盖不完整 | 中 | D |
| **RTL-ECC-003** | 错误响应可配置禁用 | 低 | D |

##### 问题RTL-ECC-001: ECC编码算法

**位置**: `ecc_memory_controller.sv:124-133`

**问题代码**:
```verilog
function automatic [ECC_WIDTH-1:0] ecc_encode(input [DATA_WIDTH-1:0] data);
    integer i;
    reg [7:0] parity;
    parity = 0;
    for (i = 0; i < DATA_WIDTH; i = i + 1) begin
        parity = parity ^ (data[i] & {8{~(i & 1)}});  // 简化算法!
    end
    ecc_encode = {parity[0], parity[1], parity[2], parity[3],
                  parity[4], parity[5], parity[6], parity[7]};
endfunction
```

**问题分析**:
- 标准Hamming码需要更复杂的奇偶校验位计算
- 当前算法可能无法检测所有双比特错误
- 缺少奇偶校验位位置优化

**标准Hamming SECDED要求**:
- P1覆盖: 位1,3,5,7,9,11,13,15,...
- P2覆盖: 位2,3,6,7,10,11,14,15,...
- P4覆盖: 位4-7,12-15,20-23,...
- P8覆盖: 位8-15,24-31,40-47,...
- P16覆盖: 位16-31,48-63,...
- 全局奇偶校验覆盖所有位

##### 问题RTL-ECC-002: BIST不完整

**位置**: `ecc_memory_controller.sv:286-306`

**问题代码**:
```verilog
always_ff @(posedge clk_i or negedge rst_n_i) begin
    if (!rst_n_i) begin
        bist_running <= 1'b0;
        bist_count <= '0;
        bist_done_o <= 1'b0;
        bist_result_o <= '0;
    end else if (bist_start_i && !bist_running) begin
        bist_running <= 1'b1;
        bist_count <= '0;
    end else if (bist_running) begin
        if (bist_count == 8'd255) begin  // 只测试256个地址!
            bist_running <= 1'b0;
            bist_done_o <= 1'b1;
            bist_result_o <= error_count[7:0];
        end else begin
            bist_count <= bist_count + 1;
        end
    end
end
```

**问题**:
- BIST仅测试256个地址,对于完整SRAM覆盖不足
- 缺少March测试算法
- 错误注入测试不完整

#### 3.3.4 RTL修改建议

```verilog
// 建议1: 使用标准Hamming SECDED编码
function automatic [ECC_WIDTH-1:0] ecc_encode(input [DATA_WIDTH-1:0] data);
    reg [63:0] d = data;
    ecc_encode[0] = ^ (d[0] | d[1] | d[3] | d[4] | d[6] | d[8] | d[10] | d[11] | 
                       d[13] | d[14] | d[16] | d[18] | d[20] | d[22] | d[24] | d[26] |
                       d[28] | d[30] | d[32] | d[34] | d[36] | d[38] | d[40] | d[42] |
                       d[44] | d[46] | d[48] | d[50] | d[52] | d[54] | d[56] | d[58] |
                       d[60] | d[62]);
    ecc_encode[1] = ^ (d[1] | d[2] | d[3] | d[5] | d[7] | d[9] | d[11] | d[13] |
                       d[15] | d[17] | d[19] | d[21] | d[23] | d[25] | d[27] | d[29] |
                       d[31] | d[33] | d[35] | d[37] | d[39] | d[41] | d[43] | d[45] |
                       d[47] | d[49] | d[51] | d[53] | d[55] | d[57] | d[59] | d[61]);
    // ... 其他校验位计算
endfunction

// 建议2: 完整MBIST
parameter int MBIST_DEPTH = 1024;  // 全地址测试
logic [9:0] mbist_addr;

always_ff @(posedge clk_i or negedge rst_n_i) begin
    if (bist_running) begin
        mbist_addr <= mbist_addr + 1;
        // 执行March测试
        run_march_test(mbist_addr);
    end
end
```

---

### 3.4 safety_island_top.sv - Safety Island顶层

#### 3.4.1 代码概述

| 项目 | 内容 |
|------|------|
| 功能 | Safety Island顶层集成 |
| 子模块 | 锁步、ECC、看门狗、错误报告 |
| 接口 | AXI主/从、IRQ、错误上报 |

#### 3.4.2 优势

| 序号 | 优势 | 说明 |
|------|------|------|
| ✅ 1 | 完整的模块集成 | 包含所有安全子模块 |
| ✅ 2 | 错误聚合 | 统一错误上报 |
| ✅ 3 | IRQ生成 | 详细的错误中断 |
| ✅ 4 | 独立时钟复位 | 主域和安全域分离 |

#### 3.4.3 发现的问题

| 问题ID | 问题描述 | 严重度 | ASIL影响 |
|--------|----------|--------|----------|
| **RTL-TOP-001** | 跨时钟域同步不足 | 高 | D+ |
| **RTL-TOP-002** | 缺少安全状态机 | 中 | D |
| **RTL-TOP-003** | 错误响应路径过长 | 中 | D |

##### 问题RTL-TOP-001: 跨时钟域同步

**位置**: `safety_island_top.sv:240-252`

**问题代码**:
```verilog
safety_watchdog u_watchdog (
    .clk_i                 (clk_safety_i),  // 安全时钟
    .rst_n_i               (rst_n_safety_i),  // 安全复位
    ...
    .lockstep_error_i      (lockstep_error),  // 来自安全时钟域
    .ecc_error_i           (ecc_error),       // 来自安全时钟域
    ...
);
```

**问题分析**: lockstep_error和ecc_error来自clk_safety_gated域,而看门狗使用clk_safety_i时钟,存在跨时钟域问题

**建议**: 添加同步器
```verilog
logic [2:0] lockstep_error_sync;
logic [2:0] ecc_error_sync;

always @(posedge clk_safety_i or negedge rst_n_safety_i) begin
    lockstep_error_sync[0] <= lockstep_error;
    lockstep_error_sync[1] <= lockstep_error_sync[0];
    lockstep_error_sync[2] <= lockstep_error_sync[1];
    
    ecc_error_sync[0] <= ecc_error;
    ecc_error_sync[1] <= ecc_error_sync[0];
    ecc_error_sync[2] <= ecc_error_sync[1];
end

safety_watchdog u_watchdog (
    ...
    .lockstep_error_i      (lockstep_error_sync[2]),
    .ecc_error_i           (ecc_error_sync[2]),
    ...
);
```

##### 问题RTL-TOP-002: 缺少安全状态机

**当前实现**: 错误仅上报IRQ,无自动安全状态转换

**建议实现**:
```verilog
typedef enum logic [2:0] {
    STATE_NORMAL,
    STATE_WARNING,
    STATE_SAFE,
    STATE_RESET
} safety_state_t;

safety_state_t safety_state;

always @(posedge clk_safety_gated or negedge rst_n_safety_synced) begin
    if (!rst_n_safety_synced) begin
        safety_state <= STATE_NORMAL;
    end else begin
        case (safety_state)
            STATE_NORMAL: begin
                if (lockstep_error || ecc_error) begin
                    safety_state <= STATE_WARNING;
                end else if (watchdog_timeout) begin
                    safety_state <= STATE_SAFE;
                end
            end
            STATE_WARNING: begin
                if (lockstep_error && ecc_error) begin
                    safety_state <= STATE_RESET;
                end else if (watchdog_timeout) begin
                    safety_state <= STATE_SAFE;
                end else if (!$stable(lockstep_error) && !$stable(ecc_error)) begin
                    safety_state <= STATE_NORMAL;
                end
            end
            STATE_SAFE: begin
                // 进入安全状态,降低频率/功能
            end
            STATE_RESET: begin
                // 触发系统复位
            end
        endcase
    end
end
```

---

### 3.5 power_monitor.sv - 电源监控器

#### 3.5.1 代码概述

| 项目 | 内容 |
|------|------|
| 功能 | 电压/温度/电流监控 |
| 通道数 | 10电压 + 8温度 + 5电流 |
| 阈值 | 高/低双阈值 |

#### 3.5.2 优势

| 序号 | 优势 | 说明 |
|------|------|------|
| ✅ 1 | 多通道监控 | 完整覆盖所有电源域 |
| ✅ 2 | 双阈值 | 警告+紧急两级 |
| ✅ 3 | 功率计算 | 动态+静态功耗估计 |

#### 3.5.3 发现的问题

| 问题ID | 问题描述 | 严重度 | ASIL影响 |
|--------|----------|--------|----------|
| **RTL-PWR-001** | 简化功率计算精度不足 | 低 | C |
| **RTL-PWR-002** | 缺少瞬态监测 | 低 | C |

---

### 3.6 safe_clock_reset.sv - 时钟复位管理

#### 3.6.1 代码概述

| 项目 | 内容 |
|------|------|
| 功能 | 时钟稳定检测、复位同步 |
| 特性 | 时钟门控、亚稳态防护 |

#### 3.6.2 优势

| 序号 | 优势 | 说明 |
|------|------|------|
| ✅ 1 | 时钟稳定检测 | 防止启动时不稳定 |
| ✅ 2 | 复位同步 | 3级同步链 |
| ✅ 3 | 复位去抖 | 防止虚假复位 |

#### 3.6.3 发现的问题

| 问题ID | 问题描述 | 严重度 | ASIL影响 |
|--------|----------|--------|----------|
| **RTL-CLK-001** | 缺少独立时钟监控 | 高 | D |
| **RTL-CLK-002** | 时钟停止检测不足 | 中 | D |

##### 问题RTL-CLK-001: 缺少独立时钟监控

**当前实现**: 仅检测时钟是否稳定,未检测时钟停止或频率异常

**建议**:
```verilog
// 独立时钟监控
logic clk_main_monitor;
logic clk_safety_monitor;
logic [31:0] clk_main_counter;
logic [31:0] clk_safety_counter;
logic rtc_clk_available;

assign rtc_clk_available = 1'b1;  // 来自32kHz RTC

// 使用RTC作为参考时钟监控主时钟
always @(posedge rtc_clk or negedge rst_n_main_i) begin
    if (!rst_n_main_i) begin
        clk_main_counter <= '0;
    end else begin
        clk_main_counter <= clk_main_counter + 1;
        if (clk_main_counter < 32'd1000 || clk_main_counter > 32'd2000) begin
            // 主时钟频率应在1000-2000 RTC周期内计数
            // 即32.768kHz参考下,1MHz时钟应计数~30次
            clk_error_detected <= 1'b1;
        end
    end
end
```

---

## 4. 发现问题汇总

### 4.1 按严重度分类

| 严重度 | 数量 | 问题ID |
|--------|------|--------|
| **高** | 6 | RTL-LS-001, RTL-LS-002, RTL-WDT-001, RTL-WDT-002, RTL-ECC-001, RTL-CLK-001 |
| **中** | 6 | RTL-LS-003, RTL-LS-004, RTL-WDT-003, RTL-WDT-004, RTL-TOP-001, RTL-TOP-002 |
| **低** | 3 | RTL-ECC-002, RTL-ECC-003, RTL-PWR-001 |

### 4.2 按模块分类

| 模块 | 高 | 中 | 低 | 总计 |
|------|----|----|----|------|
| 锁步比较器 | 2 | 2 | 0 | 4 |
| 看门狗 | 2 | 2 | 0 | 4 |
| ECC控制器 | 1 | 0 | 2 | 3 |
| 顶层集成 | 0 | 2 | 0 | 2 |
| 电源监控 | 0 | 0 | 1 | 1 |
| 时钟复位 | 1 | 1 | 0 | 2 |
| **总计** | **6** | **7** | **3** | **16** |

### 4.3 安全影响评估

| 问题 | 对FMEDA指标影响 |
|------|-----------------|
| RTL-LS-001 (无比较器自检) | DC降低5-10% |
| RTL-LS-002 (共因失效) | SPFM降低10-20% |
| RTL-ECC-001 (ECC简化) | DC降低5% |
| RTL-CLK-001 (无独立时钟监控) | DC降低3-5% |

**预计影响**: 
- SPFM: 当前51% → 改进后目标>99%
- PMHF: 当前6,891 FIT → 改进后目标<10 FIT

---

## 5. RTL修改建议

### 5.1 高优先级修改(必须)

| ID | 文件 | 修改内容 | 预计工时 |
|----|------|----------|----------|
| RTL-LS-001 | cortex_r52_lockstep.sv | 添加比较器自检逻辑 | 1周 |
| RTL-LS-002 | cortex_r52_lockstep.sv | 增加影子核独立性或TMR | 2周 |
| RTL-WDT-001 | safety_watchdog.sv | 修正混合赋值问题 | 1天 |
| RTL-WDT-002 | safety_watchdog.sv | 硬件固定使能 | 1天 |
| RTL-ECC-001 | ecc_memory_controller.sv | 使用标准Hamming编码 | 1周 |

### 5.2 中优先级修改(强烈建议)

| ID | 文件 | 修改内容 | 预计工时 |
|----|------|----------|----------|
| RTL-LS-003 | cortex_r52_lockstep.sv | 添加组合逻辑错误输出 | 3天 |
| RTL-LS-004 | cortex_r52_lockstep.sv | 直接复位触发路径 | 2天 |
| RTL-WDT-004 | safety_watchdog.sv | 直接复位请求输出 | 2天 |
| RTL-TOP-001 | safety_island_top.sv | 跨时钟域同步 | 3天 |
| RTL-TOP-002 | safety_island_top.sv | 添加安全状态机 | 2周 |

### 5.3 低优先级修改(建议)

| ID | 文件 | 修改内容 | 预计工时 |
|----|------|----------|----------|
| RTL-ECC-002 | ecc_memory_controller.sv | 完整MBIST测试 | 1周 |
| RTL-CLK-001 | safe_clock_reset.sv | 独立时钟监控 | 1周 |

---

## 6. 后续行动

### 6.1 前端设计团队行动项

| 序号 | 行动 | 负责人 | 目标日期 | 输出 |
|------|------|--------|----------|------|
| 1 | 修复高优先级问题(5项) | 前端设计 | 2026-02-15 | 更新RTL代码 |
| 2 | 修复中优先级问题(5项) | 前端设计 | 2026-03-01 | 更新RTL代码 |
| 3 | 修复低优先级问题(2项) | 前端设计 | 2026-03-15 | 更新RTL代码 |
| 4 | 重新运行FMEDA | FuSa | 2026-03-20 | 更新FMEDA报告 |

### 6.2 验证团队行动项

| 序号 | 行动 | 负责人 | 目标日期 | 输出 |
|------|------|--------|----------|------|
| 1 | 为新安全机制创建UVM测试 | DV | 2026-02-28 | 验证环境更新 |
| 2 | 故障注入验证 | DV | 2026-03-15 | 验证报告 |
| 3 | 独立安全评审 | 第三方 | 2026-04-01 | 评审报告 |

### 6.3 签核标准

RTL修改后必须满足以下条件才能签核:

| 条件 | 要求 |
|------|------|
| SPFM | ≥ 99% |
| PMHF | < 10 FIT |
| LFM | ≥ 90% |
| 诊断覆盖率 | ≥ 99% |
| 所有高优先级问题已修复 | 是 |
| 故障注入测试通过率 | 100% |

---

## 附录A: 问题详情表

| ID | 模块 | 问题描述 | 根本原因 | 影响 | 建议修复 |
|----|------|----------|----------|------|----------|
| RTL-LS-001 | 锁步比较器 | 比较器无自检 | 设计时未考虑 | 无法检测比较器故障 | 添加BIST测试逻辑 |
| RTL-LS-002 | 锁步比较器 | 双核共享时钟 | 成本考虑 | 共因失效风险高 | 独立时钟或TMR |
| RTL-LS-003 | 锁步比较器 | 错误输出延迟 | 设计选择 | FTTI违规 | 添加组合逻辑输出 |
| RTL-LS-004 | 锁步比较器 | 无直接复位 | 流程问题 | 恢复延迟 | 直接触发复位 |
| RTL-WDT-001 | 看门狗 | 混合赋值 | 编码错误 | 功能不确定 | 统一为非阻塞 |
| RTL-WDT-002 | 看门狗 | 可被禁用 | 配置设计 | 安全机制失效 | 硬件固定使能 |
| RTL-WDT-003 | 看门狗 | 无时钟监控 | 遗漏 | 无法检测时钟停止 | 添加时钟监控 |
| RTL-WDT-004 | 看门狗 | 无直接复位 | 设计缺陷 | 恢复延迟 | 添加复位请求 |
| RTL-ECC-001 | ECC控制器 | 编码简化 | 经验不足 | DC不足 | 标准Hamming码 |
| RTL-ECC-002 | ECC控制器 | BIST不完整 | 遗漏 | 覆盖不足 | 完整March测试 |
| RTL-ECC-003 | ECC控制器 | 错误可禁用 | 配置设计 | 安全机制失效 | 硬件固定 |
| RTL-TOP-001 | 顶层 | 跨时钟域 | 设计遗漏 | 亚稳态风险 | 添加同步器 |
| RTL-TOP-002 | 顶层 | 无安全状态机 | 设计不完整 | 错误响应不一致 | 添加状态机 |
| RTL-PWR-001 | 电源监控 | 计算精度 | 设计选择 | 精度不足 | 改进算法 |

---

## 审批

| 角色 | 姓名 | 签名 | 日期 |
|------|------|------|------|
| 编制 | 功能安全专家 | | 2026-01-18 |
| 前端设计负责人 | | | |
| 项目经理 | | | |

---

**文档版本**: V1.0  
**最后更新**: 2026-01-18  
**状态**: 待前端设计响应

*本文档根据ISO 26262:2018标准要求编制,是摇光SoC RTL安全审查的正式报告。*
