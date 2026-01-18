# CPU子系统设计指南

## 1. 概述

CPU子系统是YaoGuang SoC的应用处理核心，采用8核ARM Cortex-A78AE集群，提供100K+ DMIPS计算能力。

## 2. 架构要求

| 指标 | 规格 |
|------|------|
| 核心数 | 8x Cortex-A78AE |
| ISA | ARMv8.2-A |
| 主频 | 1.5-2.0 GHz (DVFS) |
| L1 Cache | 64KB I-Cache + 64KB D-Core |
| L2 Cache | 512KB/Core |
| 虚拟化 | ARM Virtualization Extensions |
| 安全 | TrustZone |

## 3. 集成要点

### 3.1 ACE4接口

```systemverilog
// Cortex-A78AE ACE4接口信号
interface cortex_a78ae_ace_if (
    input clk,
    input rst_n
);
    // AW Channel (512-bit)
    logic [31:0] awaddr;
    logic [7:0] awlen;
    logic [2:0] awsize;
    logic [1:0] awburst;
    logic [3:0] awqos;
    logic [11:0] awuser;
    logic awvalid;
    logic awready;

    // W Channel
    logic [511:0] wdata;
    logic [63:0] wstrb;
    logic wlast;
    logic wvalid;
    logic wready;

    // B Channel
    logic [1:0] bresp;
    logic [3:0] buser;
    logic bvalid;
    logic bready;

    // AR Channel
    logic [31:0] araddr;
    logic [7:0] arlen;
    logic [2:0] arsize;
    logic [1:0] arburst;
    logic [3:0] arqos;
    logic [11:0] aruser;
    logic arvalid;
    logic arready;

    // R Channel
    logic [511:0] rdata;
    logic [1:0] rresp;
    logic [3:0] ruser;
    logic rlast;
    logic rvalid;
    logic rready;
endinterface
```

### 3.2 集成清单

| 组件 | 来源 | RTL要求 |
|------|------|---------|
| Cortex-A78AE | ARM授权 | 使用商用的KEA包 |
| Snoop Control Unit | 自研 | 支持MESI一致性 |
| L2 Cache Controller | 自研 | 8路组相联，1MB |
| NoC接口 | 自研 | AXI5转ACE4 |

## 4. 开发任务

1. L2 Cache控制器设计（6周）
2. SCU一致性控制器（4周）
3. ACE4-NoC桥接器（3周）
4. CPU复位时钟方案（2周）
5. 系统集成验证（4周）
