# L3 Cache架构规格文档

**文档编号**: L3C-ARCH-001  
**版本**: V1.0  
**日期**: 2026-01-18  
**状态**: 已批准

---

## 1. 文档信息

| 项目 | 内容 |
|------|------|
| 模块名称 | L3 System Cache |
| 模块代号 | L3CACHE |
| 设计负责人 | [待定] |
| 验证负责人 | [待定] |
| 目标工艺 | TSMC 7nm FinFET |
| 目标频率 | 1.5 GHz |

---

## 2. 概述

### 2.1 模块功能

L3 System Cache是YaoGuang SoC的末级共享缓存，位于CPU、GPU、NPU等Master与DDR内存之间，提供以下功能：

- **容量**: 4-8 MB（可配置）
- **相联度**: 16路组相联
- **块大小**: 64字节
- **访问延迟**: 30-40 cycles
- **带宽**: ≥ 500 GB/s
- **一致性**: 支持Snoop协议

### 2.2 位置与作用

```
+------------------------------------------------------------------+
|                          YaoGuang SoC                            |
+------------------------------------------------------------------+
|                                                                   |
|  +--------+  +--------+  +--------+  +--------+  +--------+      |
|  | CPU    |  | GPU    |  | NPU    |  | ISP    |  | 其他   |      |
|  | Cluster|  |        |  | Cluster|  |        |  | Master |      |
|  +---+----+  +---+----+  +---+----+  +---+----+  +---+----+      |
|      |          |          |          |          |              |
|      +----------+----------+----------+----------+              |
|                         |                                      |
|                    +----+----+                                 |
|                    |  L3 Cache |  <-- 共享末级缓存              |
|                    +----+----+                                 |
|                         |                                      |
|                    +----+----+                                 |
|                    |    NoC   |                                 |
|                    +----+----+                                 |
|                         |                                      |
|                    +----+----+                                 |
|                    |  DDR     |                                 |
|                    |  Ctrl    |                                 |
|                    +----------+                                 |
+------------------------------------------------------------------+
```

### 2.3 设计目标

| 指标 | 目标值 | 说明 |
|------|--------|------|
| 容量 | 8 MB | 可配置4/6/8 MB |
| 频率 | 1.5 GHz | 与系统频率对齐 |
| 读延迟 | ≤ 35 cycles | 典型工作负载 |
| 写延迟 | ≤ 35 cycles | 写穿透/回写 |
| 带宽 | ≥ 500 GB/s | 峰值带宽 |
| 功耗 | ≤ 3 W | 典型工作负载 |
| 面积 | ≤ 6 mm² | 7nm工艺 |

---

## 3. 架构设计

### 3.1 整体架构

```
+------------------------------------------------------------------+
|                         L3 Cache Top                              |
+------------------------------------------------------------------+
|                                                                   |
|  +------------------+    +------------------+                    |
|  |  Request Handler |    |  Snoop Handler   |                    |
|  |  - 16x Masters   |    |  - CPU Snoop     |                    |
|  |  - 优先级仲裁    |    |  - 一致性协议    |                    |
|  +--------+---------+    +--------+---------+                    |
|           |                       |                               |
|  +--------v---------+    +--------v---------+                    |
|  |    Tag Array     |    |   MSHR Unit      |                    |
|  |  16-way, 8MB     |    |  Miss Status     |                    |
|  |  - Tag SRAM      |    |  - 32 entries    |                    |
|  |  - Tag CAM       |    |  - Hit-under-miss|                    |
|  +--------+---------+    +--------+---------+                    |
|           |                       |                               |
|  +--------v---------+    +--------v---------+                    |
|  |   Data Array     |    |   Replacement    |                    |
|  |  64B x 16-way    |    |  - LRU Policy    |                    |
|  |  - Data SRAM     |    |  - Pseudo-LRU    |                    |
|  +--------+---------+    +--------+---------+                    |
|           |                                                 |
|  +--------v---------+                                      |
|  |   Read/Write     |                                      |
|  |   Buffer (8x)    |                                      |
|  +--------+---------+                                      |
|           |                                                 |
|  +--------v---------+                                      |
|  |    NoC Interface |                                      |
|  |   - AXI5 Master  |                                      |
|  |   - 512-bit      |                                      |
|  +------------------+                                      |
+------------------------------------------------------------------+
```

### 3.2 参数配置

```systemverilog
// L3 Cache参数配置
parameter L3_CACHE_SIZE    = 8 * 1024 * 1024;   // 8 MB
parameter L3_WAYS          = 16;                // 16路相联
parameter L3_LINE_SIZE     = 64;                // 64B块大小
parameter L3_SETS          = L3_CACHE_SIZE / (L3_LINE_SIZE * L3_WAYS);
parameter L3_TAG_WIDTH     = 32 - $clog2(L3_LINE_SIZE) - $clog2(L3_SETS);
parameter L3_INDEX_WIDTH   = $clog2(L3_SETS);
parameter L3_OFFSET_WIDTH  = $clog2(L3_LINE_SIZE);
parameter L3_NUM_MASTERS   = 16;                // 16个主设备
parameter L3_NUM_MSHR      = 32;                // 32个MSHR条目
parameter L3_NUM_WB        = 8;                 // 8个写缓冲
parameter L3_NUM_RB        = 8;                 // 8个读缓冲
parameter L3_DATA_WIDTH    = 512;               // 512-bit数据总线
parameter L3_FREQ_TARGET   = 1500;              // 1.5 GHz
```

### 3.3 接口信号

#### 3.3.1 时钟和复位

| 信号名 | 方向 | 描述 |
|--------|------|------|
| clk | 输入 | 系统时钟 |
| rst_n | 输入 | 异步复位（低有效） |

#### 3.3.2 从接口（Master连接）

```systemverilog
// 每个Master的从接口信号
input  logic                         saxi_awvalid[16];
output logic                         saxi_awready[16];
input  logic [31:0]                  saxi_awaddr[16];
input  logic [7:0]                   saxi_awlen[16];
input  logic [2:0]                   saxi_awsize[16];
input  logic [1:0]                   saxi_awburst[16];
input  logic [3:0]                   saxi_awqos[16];

input  logic                         saxi_wvalid[16];
output logic                         saxi_wready[16];
input  logic [511:0]                 saxi_wdata[16];
input  logic [63:0]                  saxi_wstrb[16];
input  logic                         saxi_wlast[16];

output logic                         saxi_bvalid[16];
input  logic                         saxi_bready[16];
output logic [1:0]                   saxi_bresp[16];

input  logic                         saxi_arvalid[16];
output logic                         saxi_arready[16];
input  logic [31:0]                  saxi_araddr[16];
input  logic [7:0]                   saxi_arlen[16];
input  logic [2:0]                   saxi_arsize[16];
input  logic [1:0]                   saxi_arburst[16];
input  logic [3:0]                   saxi_arqos[16];

output logic                         saxi_rvalid[16];
input  logic                         saxi_rready[16];
output logic [511:0]                 saxi_rdata[16];
output logic [1:0]                   saxi_rresp[16];
output logic                         saxi_rlast[16];
```

#### 3.3.3 主接口（NoC/DDR连接）

```systemverilog
// NoC主接口
output logic                         maxi_awvalid;
input  logic                         maxi_awready;
output logic [31:0]                  maxi_awaddr;
output logic [7:0]                   maxi_awlen;
output logic [2:0]                   maxi_awsize;
output logic [1:0]                   maxi_awburst;
output logic [3:0]                   maxi_awqos;

output logic                         maxi_wvalid;
input  logic                         maxi_wready;
output logic [511:0]                 maxi_wdata;
output logic [63:0]                  maxi_wstrb;
output logic                         maxi_wlast;

input  logic                         maxi_bvalid;
output logic                         maxi_bready;
input  logic [1:0]                   maxi_bresp;

output logic                         maxi_arvalid;
input  logic                         maxi_arready;
output logic [31:0]                  maxi_araddr;
output logic [7:0]                   maxi_arlen;
output logic [2:0]                   maxi_arsize;
output logic [1:0]                   maxi_arburst;
output logic [3:0]                   maxi_arqos;

input  logic                         maxi_rvalid;
output logic                         maxi_rready;
input  logic [511:0]                 maxi_rdata;
input  logic [1:0]                   maxi_rresp;
input  logic                         maxi_rlast;
```

#### 3.3.4 控制信号

```systemverilog
// 配置和控制
input  logic [31:0]                  cfg_base_addr;      // Cache基地址
input  logic                         cache_bypass;       // Cache旁路
input  logic                         cache_flush;        // Cache刷新
input  logic                         cache_invalidate;   // Cache无效
output logic [7:0]                   cache_status;       // Cache状态
output logic                         flush_done;         // 刷新完成
output logic [31:0]                  hit_count;          // 命中计数
output logic [31:0]                  miss_count;         // 未命中计数
```

---

## 4. 功能描述

### 4.1 读操作

#### 4.1.1 读命中流程

```
1. Master发起AR请求
2. Request Handler解析地址 (Tag/Index/Offset)
3. Tag Array查找（并行16路比较）
4. 如果Tag匹配且Valid：
   - 命中！
   - 从Data Array读取数据
   - 返回R响应
   - 更新LRU
5. 如果未命中：
   - 分配MSHR
   - 发起内存读取
   - 等待数据返回
   - 更新Tag和Data
   - 返回数据
```

#### 4.1.2 读时序

```
Clock    |_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|
         
arvalid  |____|----|
arready       |____|

rvalid         |____|----|
rdata          |======data======|
rlast          |_____________|
```

### 4.2 写操作

#### 4.2.1 写策略

支持两种写策略，可配置：

**写回（Write-Back）**:
- 数据写入Cache，不立即写内存
- 仅在Cache行被替换时写回内存
- 减少内存带宽消耗

**写穿透（Write-Through）**:
- 数据同时写入Cache和内存
- 简化一致性维护
- 消耗更多内存带宽

#### 4.2.2 写分配（Write-Allocate）

- 写未命中时，分配Cache行
- 加载数据到Cache，然后更新
- 适用于写密集型工作负载

### 4.3 一致性协议

#### 4.3.1 MESI状态

| 状态 | 描述 |
|------|------|
| M (Modified) | 已修改，仅此副本，必须写回 |
| E (Exclusive) | 独占，干净，可直接修改 |
| S (Shared) | 共享，干净，多个副本 |
| I (Invalid) | 无效 |

#### 4.3.2 Snoop操作

```systemverilog
// Snoop请求类型
typedef enum logic [2:0] {
    SNOOP_INVALID,      // 无效
    SNOOP_READ_SHARED,  // 读共享
    SNOOP_READ_UNIQUE,  // 读独占
    SNOOP_WRITE_SHARED, // 写共享
    SNOOP_WRITE_UNIQUE, // 写独占
    SNOOP_PROBE         // 探测
} snoop_type_t;
```

### 4.4 替换策略

#### 4.4.1 Pseudo-LRU

```systemverilog
// 16路相联的PLRU实现
// 使用8个2-bit计数器表示16路的使用频率

module plru_16way (
    input clk,
    input rst_n,
    input [15:0] way_hit,      // 命中的way
    input hit_valid,            // 命中有效
    input [15:0] way_invalid,  // 无效的way
    output [15:0] way_replace  // 需要替换的way
);

    // PLRU树结构
    //     b0
    //   /    \
    //  b1     b2
    // / \    / \
    // w0 w1  w2 w3 ...

    reg [7:0] plru_bits;  // 8个PLRU位

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            plru_bits <= 0;
        end else if (hit_valid) begin
            // 更新PLRU位
            if (way_hit[0] || way_hit[1]) plru_bits[0] <= 0;
            if (way_hit[2] || way_hit[3]) plru_bits[0] <= 1;
            if (way_hit[0] || way_hit[2]) plru_bits[1] <= 0;
            if (way_hit[1] || way_hit[3]) plru_bits[1] <= 1;
            // ... 完整的PLRU更新逻辑
        end
    end

    // 选择替换的way
    assign way_replace = plru_bits[7] ? (plru_bits[3] ? (plru_bits[1] ? way[14:8] : way[6:0]) : 
                                          (plru_bits[1] ? way[14:8] : way[6:0])) : 
                                       (plru_bits[3] ? (plru_bits[1] ? way[14:8] : way[6:0]) : 
                                          (plru_bits[1] ? way[14:8] : way[6:0]));
endmodule
```

### 4.5 MSHR (Miss Status Handling Register)

```systemverilog
// MSHR条目结构
typedef struct packed {
    logic [31:0]     addr;           // 请求地址
    logic [9:0]      maskinfo;       // 掩码信息
    logic [3:0]      master_id;      // Master ID
    logic            valid;          // 有效位
    logic            read;           // 读请求
    logic            write;          // 写请求
    logic [7:0]      byte_en;        // 字节使能
    logic [15:0]     pending_beats;  // 待接收的beats
} mshr_entry_t;

// MSHR功能
// - 跟踪未决的Cache Miss
// - 支持Hit-Under-Miss（一个Miss处理期间处理其他请求）
// - 支持请求合并
```

### 4.6 写缓冲和读缓冲

```systemverilog
// 写缓冲 (Write Buffer)
// - 8个条目
// - 吸收写突发
// - 合并写请求
// - 流量控制

// 读缓冲 (Read Buffer)
// - 8个条目
// - 预取优化
// - 乱序完成支持
```

---

## 5. 性能指标

### 5.1 延迟分解

| 阶段 | 延迟（cycles） | 说明 |
|------|---------------|------|
| Request解析 | 1 | 地址解码和路由 |
| Tag查找 | 2 | Tag SRAM访问 |
| Tag比较 | 1 | 16路并行比较 |
| Data选择 | 1 | 多路选择器 |
| Data读出 | 2 | Data SRAM访问 |
| 响应生成 | 1 | AXI响应打包 |
| **总命中延迟** | **8-10** | 理想情况 |
| 内存访问 | 30-40 | DDR延迟 |
| **总未命中延迟** | **40-50** | 包括内存访问 |

### 5.2 带宽计算

```
峰值读带宽 = 1.5 GHz × 512 bits × 16 masters = 12 TB/s (理论)
实际带宽   = 500 GB/s (目标)
```

### 5.3 命中率目标

| 工作负载 | 目标命中率 |
|---------|-----------|
| CPU通用 | ≥ 85% |
| GPU通用 | ≥ 90% |
| NPU推理 | ≥ 95% |
| 视频处理 | ≥ 80% |

---

## 6. 功耗管理

### 6.1 功耗预算

| 模块 | 功耗 (mW) | 占比 |
|------|----------|------|
| Tag SRAM | 500 | 17% |
| Data SRAM | 2000 | 67% |
| Tag CAM | 200 | 7% |
| 控制器逻辑 | 200 | 7% |
| 时钟树 | 100 | 3% |
| **总计** | **3000** | **100%** |

### 6.2 低功耗技术

```systemverilog
// 动态门控
// - 空闲SRAM门控
// - 数据预取优化
// - Bank级门控

// 静态门控
// - 电源域隔离
// - Retention寄存器
```

---

## 7. 验证策略

### 7.1 验证层次

| 层次 | 目标 | 方法 |
|------|------|------|
| 单元验证 | 独立模块功能 | 直接测试 |
| 集成验证 | 子系统功能 | UVM |
| 系统验证 | 完整功能 | 系统级测试 |
| 性能验证 | PPA指标 | 性能模型 |

### 7.2 验证组件

- **Scoreboard**: 数据比较和顺序检查
- **Coverage**: 代码和功能覆盖率
- **Monitor**: 协议检查和时序验证
- **Reference Model**: 黄金参考模型

---

## 8. 实施计划

### 8.1 开发阶段

| 阶段 | 任务 | 周期 |
|------|------|------|
| RTL开发 | Tag Array, Data Array, Controller | 8周 |
| 验证环境 | UVM环境搭建 | 4周 |
| 功能验证 | 全部功能点覆盖 | 6周 |
| 性能验证 | 带宽/延迟测试 | 3周 |
| 形式验证 | 关键属性验证 | 2周 |
| 收敛优化 | 时序/功耗优化 | 3周 |

### 8.2 交付物

| 交付物 | 状态 |
|--------|------|
| RTL代码 | 待开发 |
| UVM环境 | 待开发 |
| 测试用例 | 待开发 |
| 时序约束 | 待开发 |
| 设计文档 | 待开发 |
| 验证报告 | 待开发 |

---

## 9. 修订历史

| 版本 | 日期 | 作者 | 描述 |
|------|------|------|------|
| V1.0 | 2026-01-18 | [待定] | 初始版本 |

---

**文档版本**: V1.0  
**最后更新**: 2026-01-18
