# NoC互联子系统设计指南

## 1. 概述

NoC（Network-on-Chip）是YaoGuang SoC的核心互联基础设施，负责连接所有处理单元和存储子系统。

## 2. 架构要求

### 2.1 性能指标

| 指标 | 要求 |
|------|------|
| 峰值带宽 | ≥ 500 GB/s |
| 延迟 | ≤ 10 cycles (平均) |
| 支持的Master数 | ≥ 16 |
| 支持的Slave数 | ≥ 32 |
| 数据位宽 | 512-bit (AXI5) |

### 2.2 拓扑结构

```
                    +------------------+
                    |   NoC Fabric     |
                    +------------------+
    +-------+  +-------+  +-------+  +-------+
    | CPU   |  | NPU   |  | GPU   |  | ISP   |
    | Cluster|  |Cluster|  |       |  |       |
    +---+---+  +---+---+  +---+---+  +---+---+
        |          |          |          |
    +---+---+  +---+---+  +---+---+  +---+---+
    | Router|  | Router|  | Router|  | Router|
    +---+---+  +---+---+  +---+---+  +---+---+
        \          |          |          /
         \         |          |         /
          \        |          |        /
           +-------+----------+-------+
                    |          |
               +----+----+ +---+---+
               | L3 Cache| | DDR Ctrl|
               +---------+ +---------+
```

## 3. 接口定义

### 3.1 AXI4/AXI5接口

```systemverilog
// Master接口模板
interface axi5_master_if (
    input clk,
    input rst_n
);
    // Write Address Channel
    logic [31:0] awaddr;
    logic [7:0] awlen;
    logic [2:0] awsize;
    logic [1:0] awburst;
    logic [3:0] awqos;
    logic awvalid;
    logic awready;

    // Write Data Channel
    logic [511:0] wdata;
    logic [63:0] wstrb;
    logic wlast;
    logic wvalid;
    logic wready;

    // Write Response Channel
    logic [1:0] bresp;
    logic bvalid;
    logic bready;

    // Read Address Channel
    logic [31:0] araddr;
    logic [7:0] arlen;
    logic [2:0] arsize;
    logic [1:0] arburst;
    logic [3:0] arqos;
    logic arvalid;
    logic arready;

    // Read Data Channel
    logic [511:0] rdata;
    logic [1:0] rresp;
    logic rlast;
    logic rvalid;
    logic rready;
endinterface
```

### 3.2 Router接口

```systemverilog
// Router端口定义
module noc_router #(
    parameter PORTS = 5,
    parameter DATA_WIDTH = 512,
    parameter FIFO_DEPTH = 16
) (
    input clk,
    input rst_n,

    // 输入端口
    axi5_if.slave in_port[PORTS],

    // 输出端口
    axi5_if.master out_port[PORTS]
);
```

## 4. 关键设计要点

### 4.1 仲裁器设计

```systemverilog
// 优先级仲裁器
module priority_arbiter #(
    parameter NUM_REQUESTERS = 8
) (
    input clk,
    input rst_n,
    input [NUM_REQUESTERS-1:0] request,
    output [NUM_REQUESTERS-1:0] grant,
    output [$clog2(NUM_REQUESTERS)-1:0] grant_id
);

    // 轮询优先级仲裁
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            grant <= 0;
            grant_id <= 0;
        end else begin
            // 轮询仲裁逻辑
            for (int i = 0; i < NUM_REQUESTERS; i++) begin
                if (request[(grant_id + i) % NUM_REQUESTERS]) begin
                    grant <= 1'b1 << ((grant_id + i) % NUM_REQUESTERS);
                    grant_id <= (grant_id + i) % NUM_REQUESTERS;
                    break;
                end
            end
        end
    end
endmodule
```

### 4.2 FIFO设计

```systemverilog
// 异步FIFO（跨时钟域）
module async_fifo #(
    parameter DATA_WIDTH = 512,
    parameter DEPTH = 16,
    parameter PTR_WIDTH = $clog2(DEPTH)
) (
    input wclk,
    input rclk,
    input wrst_n,
    input rrst_n,
    input winc,
    input [DATA_WIDTH-1:0] wdata,
    output wfull,
    input rinc,
    output [DATA_WIDTH-1:0] rdata,
    output rempty
);

    // 双端口RAM
    reg [DATA_WIDTH-1:0] fifo_ram[0:DEPTH-1];

    // 格雷码指针
    reg [PTR_WIDTH:0] wptr, wptr_gray, wptr_sync;
    reg [PTR_WIDTH:0] rptr, rptr_gray, rptr_sync;

    // 写指针
    always_ff @(posedge wclk or negedge wrst_n) begin
        if (!wrst_n) begin
            wptr <= 0;
        end else if (winc && !wfull) begin
            wptr <= wptr + 1;
        end
    end

    // 读指针同步
    always_ff @(posedge wclk) begin
        wptr_sync <= rptr_gray;
    end

    // 格雷码转换
    assign wptr_gray = wptr ^ (wptr >> 1);
    assign rptr_gray = rptr ^ (rptr >> 1);

    // 读指针
    always_ff @(posedge rclk or negedge rrst_n) begin
        if (!rrst_n) begin
            rptr <= 0;
        end else if (rinc && !rempty) begin
            rptr <= rptr + 1;
        end
    end

    // 写指针同步
    always_ff @(posedge rclk) begin
        rptr_sync <= wptr_gray;
    end

    // 满/空标志
    assign wfull = (wptr[PTR_WIDTH] != rptr_sync[PTR_WIDTH]) &&
                   (wptr[PTR_WIDTH-1:0] == rptr_sync[PTR_WIDTH-1:0]);
    assign rempty = (wptr_gray == rptr_sync);

    // RAM读写
    always_ff @(posedge wclk) begin
        if (winc && !wfull) begin
            fifo_ram[wptr[PTR_WIDTH-1:0]] <= wdata;
        end
    end

    always_ff @(posedge rclk) begin
        if (rinc && !rempty) begin
            rdata <= fifo_ram[rptr[PTR_WIDTH-1:0]];
        end
    end
endmodule
```

### 4.3 QoS实现

```systemverilog
// QoS管理器
module qos_manager #(
    parameter NUM_VC = 4,
    parameter VC_DEPTH = 8
) (
    input clk,
    input rst_n,
    input [7:0] awqos_in,
    input [7:0] arqos_in,
    output [$clog2(NUM_VC)-1:0] vc_id
);

    // QoS到VC映射
    always_comb begin
        case (awqos_in[7:6])  // 使用高2位作为QoS
            2'b11: vc_id = 3;  // 最高优先级
            2'b10: vc_id = 2;
            2'b01: vc_id = 1;
            default: vc_id = 0;
        endcase
    end
endmodule
```

## 5. 时序约束

### 5.1 SDC约束文件模板

```tcl
# NoC时钟约束
create_clock -name clk_noc -period 1.0 [get_ports clk]

# 输入延迟约束
set_input_delay -clock clk_noc -max 0.4 [get_ports {in_*_awvalid}]
set_input_delay -clock clk_noc -max 0.4 [get_ports {in_*_arvalid}]

# 输出延迟约束
set_output_delay -clock clk_noc -max 0.4 [get_ports {out_*_awready}]
set_output_delay -clock clk_noc -max 0.4 [get_ports {out_*_arready}]

# 多周期路径
set_multicycle_path -setup -from [get_pins router_inst/fifo*/wptr*] \
                    -to [get_pins router_inst/fifo*/rptr*] 2

# 虚假路径（测试端口）
set_false_path -from [get_ports test_*]
set_false_path -to [get_ports test_*]
```

## 6. 验证策略

### 6.1 UVM验证环境

```systemverilog
// NoC Scoreboard
class noc_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(noc_scoreboard)

    uvm_analysis_export #(axi_transaction) master_export[16];
    uvm_analysis_export #(axi_transaction) slave_export[32];

    // 期望队列
    axi_transaction expect_q[$];

    virtual function void write(axi_transaction tr);
        // 比较Master和Slave事务
        // 检查延迟、带宽、数据完整性
    endfunction
endclass
```

### 6.2 测试用例

1. **基本功能测试**
   - 单Master读写
   - 多Master并发访问
   - 突发传输（INCR/WRAP）

2. **性能测试**
   - 带宽测试（持续满负载）
   - 延迟测试（不同数据长度）
   - QoS优先级测试

3. **压力测试**
   - 拥塞场景（所有端口同时访问同一目标）
   - 背靠背传输
   - 长时间运行稳定性

4. **异常测试**
   - 错误响应（SLVERR/DECERR）
   - 超时处理
   - 死锁恢复

## 7. 代码规范

### 7.1 命名规则

| 类型 | 前缀 | 示例 |
|------|------|------|
| 时钟 | clk_ | clk_noc, clk_arb |
| 复位 | rst_n | rst_n, rst_sync_n |
| 有效信号 | vld | axi_vld, data_vld |
| 就绪信号 | rdy | axi_rdy, fifo_rdy |
| 计数器 | cnt | pkt_cnt, byte_cnt |
| 寄存器 | reg | reg_addr, reg_data |

### 7.2 模块模板

```systemverilog
// ============================================================================
// Module: noc_router
// Description: NoC路由器，支持多端口和QoS
// Version: 1.0
// Date: 2026-01-18
// ============================================================================

module noc_router #(
    parameter PORTS = 5,
    parameter DATA_WIDTH = 512,
    parameter FIFO_DEPTH = 16
) (
    // 时钟复位
    input  logic clk,
    input  logic rst_n,

    // 输入端口
    axi5_if.slave  in_port[PORTS],

    // 输出端口
    axi5_if.master out_port[PORTS]
);

    // 内部信号声明
    logic [PORTS-1:0] grant;
    logic [511:0] fifo_data[PORTS];
    logic fifo_full[PORTS];
    logic fifo_empty[PORTS];

    // 主体逻辑
    // ...

endmodule
```

## 8. 签核标准

### 8.1 RTL签核检查清单

- [ ] 代码风格检查（Lint）通过
- [ ] 无综合警告
- [ ] CDC分析通过
- [ ] 形式验证通过（关键模块）
- [ ] 代码覆盖率 > 95%
- [ ] 功能覆盖率 > 90%
- [ ] 时序约束完整
- [ ] 文档更新完成

### 8.2 交付物清单

| 文件 | 描述 |
|------|------|
| rtl/noc_router.sv | 路由器顶层 |
| rtl/noc_arbiter.sv | 仲裁器 |
| rtl/noc_crossbar.sv | 交叉开关 |
| rtl/async_fifo.sv | 异步FIFO |
| tb/noc_env.sv | UVM验证环境 |
| tb/noc_test.sv | 测试用例 |
| sdc/noc.sdc | 时序约束 |
| doc/design_spec.md | 设计规格 |
