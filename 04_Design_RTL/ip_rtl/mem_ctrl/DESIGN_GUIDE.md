# LPDDR5存储控制器设计指南

## 1. 概述

LPDDR5控制器负责与外部LPDDR5内存通信，提供200 GB/s带宽，支持32-64GB容量。

## 2. 架构要求

| 指标 | 规格 |
|------|------|
| 速率 | 6400 MT/s |
| 位宽 | 32-bit (2x16-bit通道) |
| 带宽 | ≥ 200 GB/s |
| 容量 | 32-64 GB |
| ECC | 支持SECDED |

## 3. 关键设计点

### 3.1 PHY接口

```systemverilog
// LPDDR5 PHY信号
interface lpddr5_phy_if ();
    input clk_p, clk_n;      // 差分时钟
    input rst_n;             // PHY复位

    // DQ数据
    inout [15:0] dq;
    inout [1:0] dqs_p, dqs_n;
    inout [1:0] dm_dbi;      // Data Mask

    // 命令地址
    output [16:0] cs_n;      // Chip Select
    output [1:0] ck_c, ck_t; // 时钟
    output [2:0] act_n;      // Activate
    output [1:0] ba;         // Bank Address
    output [6:0] bg;         // Bank Group
    output [7:0] a;          // Address
    output we_n;             // Write Enable
    output cas_n;            // Column Address Strobe
    output ras_n;            // Row Address Strobe
    output [1:0] cke;        // Clock Enable
    output odt;              // On-Die Termination
endinterface
```

### 3.2 控制器架构

```
+----------------------+
|   DDR Controller     |
+----------------------+
         |
    +----+----+
    |         |
+---v---+ +---v---+
| Write | | Read  |
| Buffer| | Buffer|
+---+---+ +---+---+
    |         |
+---v---------v---+
|   Command       |
|   Scheduler     |
+---+-------------+
    |
+---v-------------+
|   PHY           |
|   Interface     |
+---+-------------+
    |
+---v-------------+
|   LPDDR5        |
|   DRAM          |
+-----------------+
```

## 4. 开发任务

1. PHY接口控制器（8周）
2. 命令调度器（6周）
3. 写/读缓冲管理（4周）
4. 刷新和功耗管理（4周）
5. ECC编解码器（3周）
6. 验证和调优（5周）
