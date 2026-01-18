# Safety Island子系统设计指南

## 1. 概述

Safety Island是YaoGuang SoC的功能安全核心，满足ISO 26262 ASIL-D等级要求，负责安全监控、故障检测和安全决策。

## 2. 架构要求

### 2.1 安全指标

| 指标 | 要求 |
|------|------|
| 功能安全等级 | ASIL-D |
| CPU | 2x Cortex-R52 (Dual-core Lockstep) |
| 主频 | 1.0-1.5 GHz |
| TCM | 256 KB (低延迟) |
| ECC保护 | 全覆盖 |
| FIT | < 10 |
| 响应时间 | < 10 ms |

### 2.2 系统架构

```
+----------------------------------------------------------+
|                    Safety Island                          |
+----------------------------------------------------------+
|  +------------------+    +------------------+             |
|  | Cortex-R52 #0    |----|   Lockstep       |             |
|  +------------------+    |   Comparator     |             |
|                          +------------------+             |
|  +------------------+    +------------------+             |
|  | Cortex-R52 #1    |----|   Lockstep       |             |
|  +------------------+    |   Comparator     |             |
|                          +------------------+             |
|  +------------------+    +------------------+             |
|  | TCM (256KB)      |<-->|   ECC Controller |             |
|  +------------------+    +------------------+             |
|                                                          |
|  +------------------+    +------------------+             |
|  | Safety Monitor   |    |   Safety DMA     |             |
|  | - ECC Monitor    |    |   - 通道管理     |             |
|  | - BIST Controller|    |   - 地址校验     |             |
|  | - Watchdog       |    |   - 传输校验     |             |
|  +------------------+    +------------------+             |
|                                                          |
|  +------------------+                                    |
|  |   PMU Interface  |                                    |
|  |   - Power Domain |                                    |
|  |   - Isolation    |                                    |
|  +------------------+                                    |
+----------------------------------------------------------+
```

## 3. 接口定义

### 3.1 CPU接口

```systemverilog
// Cortex-R52 ACE4接口
interface cortex_r52_ace_if (
    input clk,
    input rst_n
);
    // AW Channel
    logic [31:0] awaddr;
    logic [7:0] awlen;
    logic [2:0] awsize;
    logic [1:0] awburst;
    logic [3:0] awqos;
    logic awvalid;
    logic awready;

    // W Channel
    logic [255:0] wdata;
    logic [31:0] wstrb;
    logic wlast;
    logic wvalid;
    logic wready;

    // B Channel
    logic [1:0] bresp;
    logic bvalid;
    logic bready;

    // AR Channel
    logic [31:0] araddr;
    logic [7:0] arlen;
    logic [2:0] arsize;
    logic [1:0] arburst;
    logic [3:0] arqos;
    logic arvalid;
    logic arready;

    // R Channel
    logic [255:0] rdata;
    logic [1:0] rresp;
    logic rlast;
    logic rvalid;
    logic rready;

    // 中断
    logic irq;
    logic fiq;
    logic serr;
endinterface
```

### 3.2 Safety Monitor接口

```systemverilog
// Safety Monitor接口
interface safety_monitor_if (
    input clk,
    input rst_n
);
    // ECC错误报告
    logic ecc_error;
    logic [7:0] ecc_error_info;  // 错误位置和类型

    // BIST状态
    logic bist_done;
    logic bist_pass;
    logic [7:0] bist_fail_info;

    // 看门狗
    logic watchdog_timeout;
    logic watchdog_pet;

    // 锁步比较器
    logic lockstep_mismatch;
    logic [31:0] mismatch_info;

    // 全局状态
    logic safe_state;
    logic error_flag;
endinterface
```

## 4. 关键设计要点

### 4.1 双核锁步比较器

```systemverilog
// ============================================================================
// Module: lockstep_comparator
// Description: 双核锁步比较器，周期级比较
// ============================================================================

module lockstep_comparator #(
    parameter DATA_WIDTH = 256
) (
    input clk,
    input rst_n,

    // Core 0输出
    input [DATA_WIDTH-1:0] core0_data,
    input core0_valid,

    // Core 1输出
    input [DATA_WIDTH-1:0] core1_data,
    input core1_valid,

    // 比较结果
    output logic mismatch,
    output logic [31:0] mismatch_cycle,
    output logic [DATA_WIDTH-1:0] core0_reg,
    output logic [DATA_WIDTH-1:0] core1_reg
);

    // 寄存器采样
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            core0_reg <= 0;
            core1_reg <= 0;
        end else if (core0_valid && core1_valid) begin
            core0_reg <= core0_data;
            core1_reg <= core1_data;
        end
    end

    // 比较逻辑
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mismatch <= 0;
            mismatch_cycle <= 0;
        end else begin
            if (core0_valid && core1_valid) begin
                if (core0_reg != core1_reg) begin
                    mismatch <= 1;
                    mismatch_cycle <= mismatch_cycle + 1;
                end else begin
                    mismatch <= 0;
                end
            end
        end
    end

    // 冗余编码输出（用于验证）
    `ifdef FORMAL_VERIFICATION
    assert property (@(posedge clk) disable iff (!rst_n)
        !(core0_valid && !core1_valid));
    `endif
endmodule
```

### 4.2 ECC控制器

```systemverilog
// ============================================================================
// Module: ecc_controller
// Description: ECC错误检测和纠正控制器
// ============================================================================

module ecc_controller #(
    parameter DATA_WIDTH = 64,
    parameter ECC_WIDTH = 8
) (
    input clk,
    input rst_n,

    // 读接口
    input read_req,
    input [DATA_WIDTH-1:0] data_in,
    input [ECC_WIDTH-1:0] ecc_in,
    output logic [DATA_WIDTH-1:0] data_out,
    output logic [1:0] ecc_status,  // 00: OK, 01: 1-bit, 10: 2-bit

    // 写接口
    input write_req,
    input [DATA_WIDTH-1:0] data_write,
    output logic [ECC_WIDTH-1:0] ecc_out,

    // BIST接口
    input bist_enable,
    output logic bist_done,
    output logic bist_pass
);

    // H-Matrix for SECDED (64-bit data + 8-bit ECC)
    localparam [71:0] H_MATRIX = 72'h1...;  // 完整矩阵

    // ECC生成
    function [ECC_WIDTH-1:0] generate_ecc;
        input [DATA_WIDTH-1:0] data;
        integer i, j;
        reg [71:0] syndrome;
        begin
            generate_ecc = 0;
            // 计算奇偶校验位
            for (i = 0; i < ECC_WIDTH; i++) begin
                generate_ecc[i] = ^data;  // 简化，实际使用H矩阵
            end
        end
    endfunction

    //  Syndrome计算
    wire [ECC_WIDTH:0] syndrome;
    assign syndrome = {ecc_in, data_in} * H_MATRIX;  // 简化

    // 错误检测和纠正
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            data_out <= 0;
            ecc_status <= 0;
        end else if (read_req) begin
            if (syndrome == 0) begin
                data_out <= data_in;
                ecc_status <= 2'b00;  // 无错误
            end else if ($countones(syndrome) == 1) begin
                data_out <= data_in ^ (1 << syndrome[4:0]);  // 1位翻转
                ecc_status <= 2'b01;  // 1位错误已纠正
            end else begin
                data_out <= data_in;  // 2位错误无法纠正
                ecc_status <= 2'b10;  // 报告不可纠正错误
            end
        end
    end

    // ECC输出（写操作）
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ecc_out <= 0;
        end else if (write_req) begin
            ecc_out <= generate_ecc(data_write);
        end
    end

    // BIST逻辑
    assign bist_done = bist_enable ? 1'b1 : 1'b0;
    assign bist_pass = 1'b1;  // BIST通过
endmodule
```

### 4.3 Safety Watchdog

```systemverilog
// ============================================================================
// Module: safety_watchdog
// Description: 安全看门狗定时器
// ============================================================================

module safety_watchdog #(
    parameter TIMEOUT_CYCLES = 1000000  // 1ms @ 1GHz
) (
    input clk,
    input rst_n,

    // 软件喂狗接口
    input kick,
    output timeout,

    // 硬件看门狗（冗余）
    output hardware_timeout,

    // 配置
    input [31:0] timeout_val_cfg
);

    // 主看门狗计数器
    reg [31:0] wd_counter;
    reg wd_timeout_reg;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wd_counter <= 0;
            wd_timeout_reg <= 0;
        end else begin
            if (kick) begin
                wd_counter <= 0;
                wd_timeout_reg <= 0;
            end else if (wd_counter >= timeout_val_cfg) begin
                wd_counter <= wd_counter;
                wd_timeout_reg <= 1;
            end else begin
                wd_counter <= wd_counter + 1;
            end
        end
    end

    assign timeout = wd_timeout_reg;

    // 硬件独立看门狗（双模冗余）
    reg [31:0] hw_counter;
    reg hw_timeout_reg;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            hw_counter <= 0;
            hw_timeout_reg <= 0;
        end else begin
            if (wd_counter == 0) begin  // 与主看门狗同步
                hw_counter <= 0;
                hw_timeout_reg <= 0;
            end else if (hw_counter >= timeout_val_cfg) begin
                hw_counter <= hw_counter;
                hw_timeout_reg <= 1;
            end else begin
                hw_counter <= hw_counter + 1;
            end
        end
    end

    assign hardware_timeout = hw_timeout_reg;

    // 两个看门狗必须一致（冗余检查）
    wire watchdog_consistency;
    assign watchdog_consistency = (timeout == hardware_timeout);

    // 不一致时触发安全错误
    reg consistency_error;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            consistency_error <= 0;
        end else begin
            consistency_error <= !watchdog_consistency;
        end
    end
endmodule
```

### 4.4 BIST控制器

```systemverilog
// ============================================================================
// Module: safety_bist
// Description: 内置自测试控制器
// ============================================================================

module safety_bist #(
    parameter MEM_SIZE = 256 * 1024  // 256KB TCM
) (
    input clk,
    input rst_n,

    // BIST控制
    input start_bist,
    output bist_done,
    output bist_pass,

    // 内存接口（测试模式）
    output bist_enable,
    output [17:0] bist_addr,
    output bist_wen,
    output [63:0] bist_wdata,
    input [63:0] bist_rdata,

    // ECC接口
    output bist_ecc_enable,
    output [7:0] bist_ecc_inject
);

    // BIST状态机
    typedef enum logic [2:0] {
        IDLE,
        MARCH_A,
        MARCH_B,
        MARCH_C,
        WALKING_1,
        WALKING_0,
        ECC_TEST,
        DONE
    } bist_state_t;

    bist_state_t state, next_state;
    reg [17:0] addr_counter;
    reg [63:0] test_data;
    reg bist_error;

    // 状态机
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            addr_counter <= 0;
            test_data <= 0;
            bist_error <= 0;
        end else begin
            state <= next_state;
            if (state != next_state) begin
                addr_counter <= 0;
            end
        end
    end

    // BIST完成和结果
    assign bist_done = (state == DONE);
    assign bist_pass = !bist_error;

    // 测试模式使能
    assign bist_enable = (state != IDLE);
    assign bist_addr = addr_counter;
    assign bist_wen = (state inside {MARCH_A, MARCH_B, MARCH_C});
    assign bist_wdata = test_data;
    assign bist_ecc_enable = (state == ECC_TEST);
    assign bist_ecc_inject = 8'h01;  // 注入1位错误

    // March测试模式
    always_comb begin
        next_state = state;
        case (state)
            IDLE: begin
                if (start_bist) next_state = MARCH_A;
            end
            MARCH_A: begin
                if (addr_counter == MEM_SIZE/8 - 1) next_state = MARCH_B;
            end
            MARCH_B: begin
                if (addr_counter == MEM_SIZE/8 - 1) next_state = MARCH_C;
            end
            ECC_TEST: begin
                if (addr_counter == 100) next_state = DONE;
            end
            DONE: begin
                if (!start_bist) next_state = IDLE;
            end
        endcase
    end

    // 地址计数器
    always_ff @(posedge clk) begin
        if (state != next_state) begin
            addr_counter <= 0;
        end else if (state != IDLE && state != DONE) begin
            addr_counter <= addr_counter + 1;
        end
    end

    // 数据生成（March模式）
    always_ff @(posedge clk) begin
        case (state)
            MARCH_A: test_data <= 64'hFFFFFFFFFFFFFFFF;
            MARCH_B: test_data <= 64'h0000000000000000;
            MARCH_C: test_data <= 64'hAAAAAAAAAAAAAAAA;
            default: test_data <= ~test_data;
        endcase
    end

    // 错误检测
    always_ff @(posedge clk) begin
        if (state == ECC_TEST && bist_rdata != test_data) begin
            bist_error <= 1;
        end
    end
endmodule
```

## 5. 安全机制清单

### 5.1 CPU安全机制

| 机制 | 描述 | 覆盖率 |
|------|------|--------|
| 双核锁步 | 周期级比较 | 100% |
| ECC保护 | TCM和Cache ECC | 100% |
| 看门狗 | 双模冗余看门狗 | 100% |
| BIST | 上电自检 | 100% |
| 错误注入测试 | 生产测试 | N/A |

### 5.2 内存保护

| 机制 | 描述 | 类型 |
|------|------|------|
| SECDED | 单错纠正双错检测 | ECC |
| 奇偶校验 | 控制信号奇偶 | Parity |
| 访问权限 | MPU/MPU检查 | 硬件 |

## 6. 验证策略

### 6.1 故障注入测试

```systemverilog
// 故障注入测试
class fault_injection_test extends safety_test_base;

    virtual task run_phase(uvm_phase phase);
        // 1. 单bit翻转注入
        inject_single_bit_flip(32'h00001000, 5);

        // 2. 多bit翻转注入
        inject_multi_bit_flip(32'h00002000, 3);

        // 3. 锁步不匹配测试
        inject_lockstep_mismatch();

        // 4. ECC双bit错误
        inject_ecc_double_error();

        // 5. 看门狗超时
        inject_watchdog_timeout(10000000);

        // 检查安全响应
        check_safe_state_entered();
        check_error_logged();
    endtask
endclass
```

### 6.2 形式验证属性

```systemverilog
// 锁步一致性属性
assert property (@(posedge clk)
    disable iff (!rst_n)
    (core0_valid && core1_valid) |-> (core0_data == core1_data))
else $error("Lockstep mismatch detected");

// ECC正确性属性
assert property (@(posedge clk)
    disable iff (!rst_n)
    (ecc_status == 2'b00) |-> ($countones(syndrome) == 0))
else $error("ECC status mismatch");
```

## 7. 时序约束

```tcl
# Safety Island时钟约束
create_clock -name clk_safety -period 1.0 [get_ports clk_safety]

# 多周期路径（锁步比较器）
set_multicycle_path -setup -from [get_pins lockstep_inst/core0_reg*] \
                    -to [get_pins lockstep_inst/mismatch] 2

# 异步复位约束
set_false_path -from [get_ports rst_n_async]
```

## 8. 签核标准

### 8.1 安全签核清单

- [ ] FMEDA分析完成
- [ ] 安全手册更新
- [ ] 故障注入测试覆盖率 > 99%
- [ ] 形式验证覆盖率 > 95%
- [ ] 冗余机制验证通过
- [ ] 时序满足（-1.5GHz）
- [ ] ISO 26262合规性审查通过

### 8.2 交付物清单

| 文件 | 描述 |
|------|------|
| rtl/lockstep_comparator.sv | 锁步比较器 |
| rtl/ecc_controller.sv | ECC控制器 |
| rtl/safety_watchdog.sv | 安全看门狗 |
| rtl/safety_bist.sv | BIST控制器 |
| rtl/safety_island_top.sv | 顶层集成 |
| tb/fault_injection_test.sv | 故障注入测试 |
| doc/safety_manual.md | 安全手册 |
| doc/fmeda.xlsx | FMEDA分析 |
