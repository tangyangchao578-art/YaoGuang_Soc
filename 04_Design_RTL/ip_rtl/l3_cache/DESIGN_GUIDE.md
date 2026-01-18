# L3 Cache子系统设计指南

## 1. 概述

L3 System Cache是全片共享的末级缓存，连接所有处理单元，提供4-8MB容量。

## 2. 架构要求

| 指标 | 规格 |
|------|------|
| 容量 | 4-8 MB |
| 相联度 | 16路组相联 |
| 块大小 | 64B |
| 延迟 | 30-40 cycles |
| 带宽 | ≥ 500 GB/s |
| 共享范围 | 全片共享 |

## 3. 接口定义

```systemverilog
// L3 Cache接口
interface l3_cache_if (input clk, input rst_n);
    // 多个AXI从接口（来自各Master）
    axi5_if.slave master_if[16];

    // 主接口（连接DDR）
    axi5_if.master mem_if;

    // 控制信号
    logic sram_bypass;
    logic cache_flush;
    logic [7:0] cache_status;
endinterface
```

## 4. 关键设计点

### 4.1 Cache控制器

```systemverilog
module l3_cache_controller #(
    parameter SIZE = 8 * 1024 * 1024,  // 8MB
    parameter WAYS = 16,
    parameter LINE_SIZE = 64
) (
    input clk,
    input rst_n,

    // 从接口
    axi5_if.slave snoop_if,

    // 主接口
    axi5_if.master mem_if,

    // SRAM接口
    output logic tag_wen,
    output logic [21:0] tag_addr,
    output logic [22:0] tag_wdata,
    input [22:0] tag_rdata,

    output logic data_wen,
    output logic [16:0] data_addr,
    output [511:0] data_wdata,
    input [511:0] data_rdata
);

    // Tag SRAM: 22-bit tag + 1-bit valid + 1-bit dirty
    // Data SRAM: 512-bit data

    // Miss处理
    always_ff @(posedge clk) begin
        if (cache_miss) begin
            // 发起内存读取
            mem_if.arvalid <= 1;
            mem_if.araddr <= miss_addr;
        end
    end
endmodule
```

## 5. 开发任务

1. Tag SRAM阵列（3周）
2. Data SRAM阵列（3周）
3. Cache控制器（6周）
4. 替换策略（LRU）（4周）
5. 一致性协议（MOESI）（6周）
6. 性能优化（4周）
