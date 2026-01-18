# NPU集群子系统设计指南

## 1. 概述

NPU（Neural Processing Unit）是YaoGuang SoC的AI推理加速器，提供300 TOPS INT8算力，支持CNN、Transformer和RNN等神经网络模型。

## 2. 架构要求

### 2.1 性能指标

| 指标 | 要求 |
|------|------|
| 总算力 | 300 TOPS INT8 (4 clusters) |
| 单集群算力 | 75 TOPS INT8 |
| FP16算力 | 150 TFLOPS |
| MAC单元数 | 1024 INT8 MACs/cluster |
| 片上SRAM | 4 MB/cluster |
| 频率 | 1.0-1.5 GHz |
| 稀疏加速 | 1.5-2x 有效算力提升 |

### 2.2 系统架构

```
+------------------------------------------------------------------+
|                        NPU Cluster                                |
+------------------------------------------------------------------+
|  +------------------+                                            |
|  |   Control Unit   |                                            |
|  | - 指令解码       |                                            |
|  | - 数据流控制     |                                            |
|  | - 调度器         |                                            |
|  +--------+---------+                                            |
|           |                                                       |
|  +--------+---------+                                            |
|  |  MAC Array       |  <-- 1024 INT8 MACs                        |
|  |  (16x16 Systolic)|                                            |
|  +--------+---------+                                            |
|           |                                                       |
|  +--------+---------+                                            |
|  |  Activation Unit |                                            |
|  |  - ReLU/PReLU    |                                            |
|  |  - BatchNorm     |                                            |
|  |  - Quantization  |                                            |
|  +--------+---------+                                            |
|           |                                                       |
|  +--------+---------+                                            |
|  |  Sparse Engine   |                                            |
|  |  - 结构化稀疏    |                                            |
|  |  - 非结构化稀疏  |                                            |
|  +--------+---------+                                            |
|           |                                                       |
|  +--------+---------+    +--------+---------+                    |
|  | Weight SRAM      |    | Activation SRAM |                    |
|  | (2 MB)           |    | (2 MB)          |                    |
|  +------------------+    +------------------+                    |
|                                                                  |
|  +------------------+    +------------------+                    |
|  |   NoC Interface  |    |  ECC Protection  |                    |
|  |   - AXI4 Master  |    |  - SECDED        |                    |
|  |   - 512-bit      |    |  - 端到端保护    |                    |
|  +------------------+    +------------------+                    |
+------------------------------------------------------------------+
```

## 3. 接口定义

### 3.1 NoC接口

```systemverilog
// NPU Cluster AXI4接口
interface npu_cluster_if (
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

    // 中断和状态
    logic irq;
    logic done;
    logic busy;
    logic [7:0] status;
endinterface
```

### 3.2 配置接口

```systemverilog
// NPU配置寄存器映射
typedef struct packed {
    logic [31:0] base_addr_w;       // 权重基地址
    logic [31:0] base_addr_a;       // 激活值基地址
    logic [31:0] base_addr_o;       // 输出基地址
    logic [15:0] input_h;           // 输入高度
    logic [15:0] input_w;           // 输入宽度
    logic [15:0] output_h;          // 输出高度
    logic [15:0] output_w;          // 输出宽度
    logic [9:0] kernel_h;           // 卷积核高度
    logic [9:0] kernel_w;           // 卷积核宽度
    logic [7:0] channels;           // 通道数
    logic [7:0] strides;            // 步长
    logic [3:0] op_type;            // 操作类型
    logic [3:0] act_func;           // 激活函数
    logic quant_mode;               // 量化模式
    logic sparse_en;                // 稀疏使能
    logic start;                    // 启动信号
} npu_config_t;
```

## 4. 关键设计要点

### 4.1 MAC阵列（脉动阵列）

```systemverilog
// ============================================================================
// Module: mac_array
// Description: 16x16脉动MAC阵列
// ============================================================================

module mac_array #(
    parameter ARRAY_H = 16,
    parameter ARRAY_W = 16,
    parameter DATA_WIDTH = 8  // INT8
) (
    input clk,
    input rst_n,

    // 权重输入（列方向）
    input [DATA_WIDTH-1:0] weight_in[ARRAY_W],
    input weight_valid,

    // 激活值输入（行方向）
    input [DATA_WIDTH-1:0] act_in[ARRAY_H],
    input act_valid,

    // 累加输出
    output logic [31:0] accum_out[ARRAY_H][ARRAY_W],
    output logic accum_valid
);

    // MAC单元阵列
    genvar i, j;
    generate
        for (i = 0; i < ARRAY_H; i++) begin : ROW
            for (j = 0; j < ARRAY_W; j++) begin : COL
                mac_cell #(
                    .DATA_WIDTH(DATA_WIDTH)
                ) mac_inst (
                    .clk(clk),
                    .rst_n(rst_n),
                    .weight_in(j == 0 ? weight_in[j] : weight_reg[i][j-1]),
                    .act_in(i == 0 ? act_in[i] : act_reg[i-1][j]),
                    .partial_sum_in(i == 0 || j == 0 ? 32'b0 : accum_reg[i][j-1] + accum_reg[i-1][j]),
                    .weight_out(weight_reg[i][j]),
                    .act_out(act_reg[i][j]),
                    .partial_sum_out(accum_reg[i][j])
                );
            end
        end
    endgenerate

    // 输出寄存器
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            accum_out <= 0;
            accum_valid <= 0;
        end else begin
            accum_out <= accum_reg;
            accum_valid <= weight_valid && act_valid;
        end
    end

    // 内部寄存器
    reg [DATA_WIDTH-1:0] weight_reg[ARRAY_H][ARRAY_W];
    reg [DATA_WIDTH-1:0] act_reg[ARRAY_H][ARRAY_W];
    reg [31:0] accum_reg[ARRAY_H][ARRAY_W];
endmodule

// MAC单元
module mac_cell #(
    parameter DATA_WIDTH = 8
) (
    input clk,
    input rst_n,
    input [DATA_WIDTH-1:0] weight_in,
    input [DATA_WIDTH-1:0] act_in,
    input [31:0] partial_sum_in,
    output [DATA_WIDTH-1:0] weight_out,
    output [DATA_WIDTH-1:0] act_out,
    output [31:0] partial_sum_out
);

    // 乘法
    wire [15:0] product;
    assign product = $signed(weight_in) * $signed(act_in);

    // 累加
    reg [31:0] sum_reg;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sum_reg <= 0;
        end else begin
            sum_reg <= partial_sum_in + $signed(product);
        end
    end

    // 输出寄存
    assign weight_out = weight_in;
    assign act_out = act_in;
    assign partial_sum_out = sum_reg;
endmodule
```

### 4.2 稀疏引擎

```systemverilog
// ============================================================================
// Module: sparse_engine
// Description: 稀疏计算引擎，支持结构化和非结构化稀疏
// ============================================================================

module sparse_engine #(
    parameter DATA_WIDTH = 8,
    parameter NUM_ELEMENTS = 1024
) (
    input clk,
    input rst_n,

    // 输入数据
    input [DATA_WIDTH-1:0] data_in[NUM_ELEMENTS],
    input data_valid,

    // 稀疏索引（结构化稀疏：2:4）
    input [9:0] sparse_idx_in[NUM_ELEMENTS/4],

    // 输出数据
    output [DATA_WIDTH-1:0] data_out[NUM_ELEMENTS/2],
    output data_valid_out,

    // 配置
    input sparse_mode,           // 0: 结构化, 1: 非结构化
    input [1:0] sparse_ratio,    // 00: 2:4, 01: 4:8
    input sparse_en
);

    // 非结构化稀疏：零值检测和跳过
    generate
        if (!sparse_en) begin : NO_SPARSE
            assign data_out = data_in[NUM_ELEMENTS/2:0];
            assign data_valid_out = data_valid;
        end else begin : SPARSE_ENABLE
            // 零值计数器
            reg [9:0] zero_count[NUM_ELEMENTS];
            reg [9:0] non_zero_count;

            // 检测零值
            always_ff @(posedge clk) begin
                for (int i = 0; i < NUM_ELEMENTS; i++) begin
                    zero_count[i] <= (data_in[i] == 0) ? zero_count[i] + 1 : zero_count[i];
                end
            end

            // 压缩输出（移除零值）
            reg [DATA_WIDTH-1:0] compressed_data[NUM_ELEMENTS];
            reg [9:0] compressed_idx;
            reg compressed_valid;

            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    compressed_data <= 0;
                    compressed_idx <= 0;
                    compressed_valid <= 0;
                end else if (data_valid) begin
                    compressed_valid <= 1;
                    for (int i = 0; i < NUM_ELEMENTS; i++) begin
                        if (data_in[i] != 0) begin
                            compressed_data[compressed_idx] <= data_in[i];
                            compressed_idx <= compressed_idx + 1;
                        end
                    end
                end else begin
                    compressed_valid <= 0;
                end
            end

            // 稀疏率统计
            wire [7:0] sparsity;
            assign sparsity = (non_zero_count * 100) / NUM_ELEMENTS;

            assign data_out = compressed_data;
            assign data_valid_out = compressed_valid;
        end
    endgenerate
endmodule
```

### 4.3 激活函数单元

```systemverilog
// ============================================================================
// Module: activation_unit
// Description: 激活函数处理单元
// ============================================================================

module activation_unit #(
    parameter DATA_WIDTH = 32
) (
    input clk,
    input rst_n,

    // 输入数据
    input [DATA_WIDTH-1:0] data_in,
    input data_valid,

    // 输出数据
    output [DATA_WIDTH-1:0] data_out,
    output data_valid_out,

    // 配置
    input [3:0] act_type,     // 0: ReLU, 1: PReLU, 2: LeakyReLU, 3: Sigmoid, 4: Tanh
    input [15:0] act_param,   // 激活函数参数
    input quant_en,           // 量化使能
    input [7:0] quant_scale,  // 量化 scale
    input [7:0] quant_zero    // 量化 zero point
);

    // 激活函数选择
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            data_out <= 0;
        end else if (data_valid) begin
            case (act_type)
                4'd0: data_out <= relu(data_in);
                4'd1: data_out <= prelu(data_in, act_param);
                4'd2: data_out <= leaky_relu(data_in, act_param);
                4'd3: data_out <= sigmoid(data_in);
                4'd4: data_out <= tanh(data_in);
                default: data_out <= relu(data_in);
            endcase
        end
    end

    // 量化后处理
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            data_out <= 0;
            data_valid_out <= 0;
        end else if (quant_en && data_valid) begin
            // INT8量化
            logic [31:0] quantized;
            quantized = (data_in / quant_scale) + quant_zero;
            data_out <= quantized[7:0];
            data_valid_out <= 1;
        end else begin
            data_valid_out <= data_valid;
        end
    end

    // ReLU函数
    function [DATA_WIDTH-1:0] relu;
        input [DATA_WIDTH-1:0] x;
        relu = (x[DATA_WIDTH-1]) ? 0 : x;
    endfunction

    // PReLU函数
    function [DATA_WIDTH-1:0] prelu;
        input [DATA_WIDTH-1:0] x;
        input [15:0] alpha;
        prelu = x[DATA_WIDTH-1] ? (x * alpha) >> 8 : x;
    endfunction

    // Leaky ReLU函数
    function [DATA_WIDTH-1:0] leaky_relu;
        input [DATA_WIDTH-1:0] x;
        input [15:0] alpha;
        leaky_relu = x[DATA_WIDTH-1] ? (x * alpha) >> 8 : x;
    endfunction

    // Sigmoid函数（查表法）
    function [DATA_WIDTH-1:0] sigmoid;
        input [DATA_WIDTH-1:0] x;
        // 简化的查表实现
        sigmoid = (x > 0) ? 32'h3F800000 : 32'h00000000;
    endfunction

    // Tanh函数（查表法）
    function [DATA_WIDTH-1:0] tanh;
        input [DATA_WIDTH-1:0] x;
        tanh = x;
    endfunction
endmodule
```

### 4.4 数据流控制器

```systemverilog
// ============================================================================
// Module: npu_controller
// Description: NPU控制单元，负责指令解码和数据流调度
// ============================================================================

module npu_controller #(
    parameter NUM_CLUSTERS = 4
) (
    input clk,
    input rst_n,

    // 配置接口
    input npu_config_t config,
    input config_valid,

    // 状态输出
    output logic busy,
    output logic done,
    output logic [7:0] status,
    output logic irq,

    // SRAM接口
    output logic sram_wen,
    output logic [19:0] sram_addr,
    output logic [511:0] sram_wdata,
    input [511:0] sram_rdata,

    // MAC阵列控制
    output logic mac_start,
    output logic mac_stop,
    input mac_done,

    // NoC接口
    axi4_if.master noc_if
);

    // 状态机
    typedef enum logic [4:0] {
        IDLE,
        FETCH_WEIGHT,
        FETCH_ACT,
        COMPUTE,
        STORE_RESULT,
        CHECK_DONE,
        ERROR
    } state_t;

    state_t state, next_state;
    reg [31:0] pc;
    reg [31:0] weight_addr;
    reg [31:0] act_addr;
    reg [31:0] output_addr;
    reg [15:0] loop_counter;

    // 主状态机
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            pc <= 0;
        end else begin
            state <= next_state;
        end
    end

    // 状态机转换
    always_comb begin
        next_state = state;
        case (state)
            IDLE: begin
                if (config.start) next_state = FETCH_WEIGHT;
                else if (config_valid) next_state = IDLE;
            end
            FETCH_WEIGHT: begin
                if (weight_fetch_done) next_state = FETCH_ACT;
            end
            FETCH_ACT: begin
                if (act_fetch_done) next_state = COMPUTE;
            end
            COMPUTE: begin
                if (mac_done) next_state = STORE_RESULT;
            end
            STORE_RESULT: begin
                if (result_store_done) next_state = CHECK_DONE;
            end
            CHECK_DONE: begin
                if (!loop_end) next_state = FETCH_WEIGHT;
                else next_state = IDLE;
            end
            ERROR: begin
                if (config.start) next_state = IDLE;
            end
        endcase
    end

    // NoC读请求（权重）
    assign noc_if.arvalid = (state == FETCH_WEIGHT);
    assign noc_if.araddr = weight_addr;
    assign noc_if.arlen = 8'd15;  // 16 beats burst
    assign noc_if.arsize = 3'd6;  // 64 bytes
    assign noc_if.arburst = 2'b01;  // INCR

    // NoC读请求（激活值）
    assign noc_if.arvalid = (state == FETCH_ACT);
    assign noc_if.araddr = act_addr;
    assign noc_if.arlen = 8'd15;
    assign noc_if.arsize = 3'd6;
    assign noc_if.arburst = 2'b01;

    // NoC写请求（结果）
    assign noc_if.awvalid = (state == STORE_RESULT);
    assign noc_if.awaddr = output_addr;
    assign noc_if.awlen = 8'd15;
    assign noc_if.awsize = 3'd6;
    assign noc_if.awburst = 2'b01;

    // 状态输出
    assign busy = (state != IDLE);
    assign done = (state == IDLE) && config.start;
    assign status = {3'b000, state};
    assign irq = (state == IDLE) && config.start;
endmodule
```

### 4.5 低功耗设计

```systemverilog
// 时钟门控单元
module mac_clock_gating (
    input clk,
    input en,
    output clk_gated
);

    // 门控锁存器
    latch_enable #(.WIDTH(1)) gate_latch (
        .clk(clk),
        .en(en),
        .d(1'b1),
        .q(gate_latch_out)
    );

    // 时钟门控缓冲
    assign clk_gated = clk & gate_latch_out;
endmodule

// 使用门控的MAC阵列
generate
    for (i = 0; i < ARRAY_H; i++) begin : ROW_GATED
        for (j = 0; j < ARRAY_W; j++) begin : COL_GATED
            always_ff @(posedge clk_gated or negedge rst_n) begin
                if (!rst_n) begin
                    accum_reg[i][j] <= 0;
                end else begin
                    accum_reg[i][j] <= partial_sum_in + $signed(product);
                end
            end
        end
    end
endgenerate
```

## 5. 验证策略

### 5.1 参考模型

```systemverilog
// NPU参考模型（C++模型绑定）
class npu_reference_model extends uvm_component;
    `uvm_component_utils(npu_reference_model)

    // Python/C++模型接口
    import "DPI-C" function void npu_model_init();
    import "DPI-C" function void npu_model_run(
        input int input_h, input int input_w,
        input int kernel_h, input int kernel_w,
        input int stride, input int padding,
        input bit [31:0] weight_ptr,
        input bit [31:0] input_ptr,
        input bit [31:0] output_ptr
    );
    import "DPI-C" function int npu_model_check();

    virtual function void run_phase(uvm_phase phase);
        // 运行参考模型
        npu_model_run(config.input_h, config.input_w, ...);
        // 比较结果
        error_count = npu_model_check();
    endfunction
endclass
```

### 5.2 测试用例

| 测试用例 | 描述 | 预期结果 |
|---------|------|---------|
| 单卷积 | 3x3卷积，FP32 | 精度 < 1% |
| 深度可分离卷积 | MobileNet风格 | 精度 < 1% |
| Transformer | Multi-Head Attention | 精度 < 1% |
| 稀疏卷积 | 50%零值 | 2x加速 |
| 量化推理 | INT8量化 | 精度 < 2% |
| 边界测试 | 各种边界条件 | 无错误 |
| 压力测试 | 长时间运行 | 无溢出 |

## 6. 时序约束

```tcl
# NPU时钟约束
create_clock -name clk_npu -period 1.0 [get_ports clk_npu]

# 关键路径约束
set_max_delay -from [get_pins mac_array*/mac_inst*/partial_sum*] \
               -to [get_pins mac_array*/mac_inst*/sum_reg*] 0.8

# MAC阵列流水线约束
set_multicycle_path -setup -from [get_pins mac_array*/mac_inst*/product*] \
                    -to [get_pins mac_array*/mac_inst*/sum_reg*] 1

# SRAM接口约束
set_input_delay -clock clk_npu -max 0.5 [get_ports sram_rdata*]
set_output_delay -clock clk_npu -max 0.5 [get_ports sram_addr*]
```

## 7. 签核标准

### 7.1 性能签核

- [ ] 算力达到300 TOPS（4集群）
- [ ] 稀疏加速比 > 1.5x
- [ ] 频率达到1.0 GHz
- [ ] 功耗 < 25W（4集群）
- [ ] 面积 < 36 mm²

### 7.2 功能签核

- [ ] 代码覆盖率 > 95%
- [ ] 功能覆盖率 > 90%
- [ ] 精度验证通过（< 1%误差）
- [ ] 稀疏计算验证通过

### 7.3 交付物清单

| 文件 | 描述 |
|------|------|
| rtl/mac_array.sv | MAC阵列 |
| rtl/sparse_engine.sv | 稀疏引擎 |
| rtl/activation_unit.sv | 激活函数单元 |
| rtl/npu_controller.sv | 控制单元 |
| rtl/npu_cluster_top.sv | 集群顶层 |
| tb/npu_scoreboard.sv | 记分板 |
| tb/npu_ref_model.sv | 参考模型 |
| tb/npu_accuracy_test.sv | 精度测试 |
| doc/npu_arch.md | 架构文档 |
