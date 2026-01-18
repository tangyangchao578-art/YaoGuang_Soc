# 摇光(YaoGuang) SoC RTL 开发规范

## 文档信息

| 项目 | 内容 |
|------|------|
| 文档版本 | V1.0 |
| 创建日期 | 2026-01-19 |
| 最后更新 | 2026-01-19 |
| 状态 | 草稿 |
| 负责人 | RTL 团队负责人 |
| 关联文档 | 架构规格书 (01_Architecture_Spec_YaoGuang_SoC.md) |

---

## 1. 概述

### 1.1 RTL 开发目标

| 指标 | 目标值 | 备注 |
|------|--------|------|
| **编码标准** | SystemVerilog | IEEE 1800-2017 |
| **代码行数** | ~ 1M LOC | 估算 |
| **模块数量** | 200+ | 包括子模块 |
| **开发周期** | 2026-03 至 2026-08 | 6 个月 |
| **冻结时间** | 2026-08-31 | RTL 冻结 |
| **Lint 通过率** | 100% | 0 警告 |
| **CDC 通过率** | 100% | 0 违例 |

### 1.2 开发原则

1. **同步设计优先**: 优先使用同步设计，避免异步逻辑
2. **可综合代码**: 所有代码必须可综合，避免仿真专用语法
3. **参数化设计**: 支持参数化配置，提高复用性
4. **时钟域清晰**: 明确时钟域边界，妥善处理跨时钟域
5. **复位策略统一**: 使用统一的复位策略

---

## 2. 代码风格规范

### 2.1 文件命名规范

| 文件类型 | 命名格式 | 示例 |
|----------|----------|------|
| **RTL 模块** | `<module_name>.sv` | `cpu_core.sv` |
| **接口定义** | `<if_name>_if.sv` | `axi4_if.sv` |
| **封装** | `<pkg_name>_pkg.sv` | `common_def_pkg.sv` |
| **测试平台** | `<module_name>_tb.sv` | `cpu_core_tb.sv` |

### 2.2 模块命名规范

| 规则 | 格式 | 示例 |
|------|------|------|
| **模块名** | 小写 + 下划线 | `cpu_core` |
| **端口名** | 小写 + 下划线 | `clk_sys` |
| **信号名** | 小写 + 下划线 | `data_valid` |
| **参数名** | 大写 + 下划线 | `DATA_WIDTH` |
| **宏定义** | 大写 + 下划线 | ``define FIFO_DEPTH` |

### 2.3 信号命名约定

| 信号类型 | 前缀 | 示例 |
|----------|------|------|
| **时钟** | `clk_` | `clk_sys`, `clk_core` |
| **复位** | `rst_n` | `rst_sys_n`, `rst_core_n` |
| **使能** | `en_` | `en_core` |
| **有效** | `_valid` | `data_valid` |
| **就绪** | `_ready` | `data_ready` |
| **中断** | `int_` | `int_error` |
| **锁步** | `ls_` | `ls_match` |

---

## 3. RTL 编码规范

### 3.1 模块模板

```systemverilog
// 文件头注释
// ============================================================================
// Module: cpu_core
// Description: CPU 核心处理单元
// Author: CPU Team
// Version: V1.0
// Date: 2026-03-01
// ============================================================================

module cpu_core #(
    parameter DATA_WIDTH = 64,
    parameter ADDR_WIDTH = 32
) (
    // 时钟复位
    input  logic                         clk,
    input  logic                         rst_n,
    
    // 接口
    input  logic                         en,
    output logic                         int_error,
    
    // 数据接口
    input  logic [DATA_WIDTH-1:0]         data_in,
    input  logic                         data_in_valid,
    output logic                         data_in_ready,
    output logic [DATA_WIDTH-1:0]         data_out,
    output logic                         data_out_valid,
    input  logic                         data_out_ready
);

    // 内部信号声明
    logic [DATA_WIDTH-1:0]  data_reg;
    logic                  data_valid_reg;
    
    // 参数检查
    initial begin
        if (DATA_WIDTH < 32) begin
            $error("DATA_WIDTH must be at least 32");
        end
    end

    // 逻辑实现
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            data_reg        <= '0;
            data_valid_reg  <= 1'b0;
        end else if (en && data_in_valid && data_in_ready) begin
            data_reg        <= data_in;
            data_valid_reg  <= 1'b1;
        end
    end
    
    // 输出赋值
    assign data_out        = data_reg;
    assign data_out_valid  = data_valid_reg;

endmodule
```

### 3.2 端口声明顺序

```systemverilog
module example_module (
    // 1. 时钟复位
    input  logic clk,
    input  logic rst_n,
    
    // 2. 控制信号
    input  logic en,
    output logic int_error,
    
    // 3. 输入信号
    input  logic [31:0] data_in,
    input  logic         data_in_valid,
    
    // 4. 输出信号
    output logic [31:0] data_out,
    output logic         data_out_valid
);
```

### 3.3 时钟复位规范

```systemverilog
// 复位规范
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        // 复位逻辑
    end else begin
        // 正常逻辑
    end
end

// 避免在组合逻辑中直接使用时钟
// 错误示例:
// assign q = clk ? d : q;

// 正确示例:
// always_ff @(posedge clk) begin
//     q <= d;
// end
```

### 3.4 跨时钟域处理

```systemverilog
// 方法 1: 打拍器 (同步器)
logic [2:0] async_sync;

always_ff @(posedge clk_dst or negedge rst_n) begin
    if (!rst_n) begin
        async_sync <= '0;
    end else begin
        async_sync <= {async_sync[1:0], async_sig_src};
    end
end

// 方法 2: 握手协议
// 使用 req/ack 握手
```

---

## 4. 接口规范

### 4.1 AXI4 接口

```systemverilog
// AXI4 接口封装
interface axi4_if #(parameter DATA_WIDTH = 32, parameter ADDR_WIDTH = 32);
    // 写地址通道
    logic                     awvalid;
    logic                     awready;
    logic [ADDR_WIDTH-1:0]    awaddr;
    logic [7:0]               awlen;
    logic [2:0]               awsize;
    logic [1:0]               awburst;
    
    // 写数据通道
    logic                     wvalid;
    logic                     wready;
    logic [DATA_WIDTH-1:0]    wdata;
    logic [(DATA_WIDTH/8)-1:0] wstrb;
    logic                     wlast;
    
    // 写响应通道
    logic                     bvalid;
    logic                     bready;
    logic [1:0]               bresp;
    
    // 读地址通道
    logic                     arvalid;
    logic                     arready;
    logic [ADDR_WIDTH-1:0]    araddr;
    logic [7:0]               arlen;
    logic [2:0]               arsize;
    logic [1:0]               arburst;
    
    // 读数据通道
    logic                     rvalid;
    logic                     rready;
    logic [DATA_WIDTH-1:0]    rdata;
    logic [1:0]               rresp;
    logic                     rlast;
    
    modport master (
        output awvalid, awaddr, awlen, awsize, awburst,
        input  awready,
        output wvalid, wdata, wstrb, wlast,
        input  wready,
        input  bvalid, bresp,
        output bready,
        output arvalid, araddr, arlen, arsize, arburst,
        input  arready,
        input  rvalid, rdata, rresp, rlast,
        output rready
    );
    
    modport slave (
        input  awvalid, awaddr, awlen, awsize, awburst,
        output awready,
        input  wvalid, wdata, wstrb, wlast,
        output wready,
        output bvalid, bresp,
        input  bready,
        input  arvalid, araddr, arlen, arsize, arburst,
        output arready,
        output rvalid, rdata, rresp, rlast,
        input  rready
    );
endinterface
```

### 4.2 APB4 接口

```systemverilog
interface apb4_if #(parameter DATA_WIDTH = 32, parameter ADDR_WIDTH = 12);
    logic                     pclk;
    logic                     preset_n;
    
    logic [ADDR_WIDTH-1:0]    paddr;
    logic [DATA_WIDTH-1:0]    pwdata;
    logic [DATA_WIDTH-1:0]    prdata;
    logic                     pwrite;
    logic                     psel;
    logic                     penable;
    logic                     pready;
    logic [3:0]               pstrb;
    
    modport master (
        output paddr, pwdata, pwrite, psel, penable, pstrb,
        input  prdata, pready
    );
    
    modport slave (
        input  paddr, pwdata, pwrite, psel, penable, pstrb,
        output prdata, pready
    );
endinterface
```

---

## 5. 封装定义

### 5.1 常用封装

```systemverilog
package common_def_pkg;
    // 数据位宽定义
    parameter int DATA_WIDTH_8   = 8;
    parameter int DATA_WIDTH_16  = 16;
    parameter int DATA_WIDTH_32  = 32;
    parameter int DATA_WIDTH_64  = 64;
    parameter int DATA_WIDTH_128 = 128;
    parameter int DATA_WIDTH_256 = 256;
    parameter int DATA_WIDTH_512 = 512;
    
    // 地址位宽定义
    parameter int ADDR_WIDTH_12 = 12;
    parameter int ADDR_WIDTH_16 = 16;
    parameter int ADDR_WIDTH_32 = 32;
    parameter int ADDR_WIDTH_64 = 64;
    
    // 缓存线大小
    parameter int CACHE_LINE_SIZE = 64;
    
    // 常用参数
    parameter int NUM_CPU_CORES = 8;
    parameter int NUM_NPU_CLUSTERS = 4;
    
    // 函数定义
    function automatic int clog2(input int value);
        int result = 0;
        while (value > 1) begin
            value >>= 1;
            result++;
        end
        return result;
    endfunction
    
    // 类型定义
    typedef logic [DATA_WIDTH_32-1:0]  data32_t;
    typedef logic [DATA_WIDTH_64-1:0]  data64_t;
    typedef logic [ADDR_WIDTH_32-1:0]  addr32_t;
    typedef logic [ADDR_WIDTH_64-1:0]  addr64_t;
endpackage
```

---

## 6. 时序约束

### 6.1 时钟约束模板

```tcl
# YaoGuang SoC 时序约束文件
# Version: V1.0
# Date: 2026-03-01

# 定义时钟
create_clock -period 5.00 -name clk_sys [get_ports clk_sys]
create_clock -period 5.00 -name clk_core [get_ports clk_core]
create_clock -period 5.00 -name clk_npu [get_ports clk_npu]

# 时钟分组
group_path -name CLK_SYS -group clk_sys
group_path -name CLK_CORE -group clk_core
group_path -name CLK_NPU -group clk_npu

# 时钟关系（异步时钟）
set_clock_groups -asynchronous -group {CLK_SYS} -group {CLK_CORE}

# 输入延迟
set_input_delay -clock clk_sys -max 2.0 [get_ports data_in*]
set_input_delay -clock clk_sys -min 0.5 [get_ports data_in*]

# 输出延迟
set_output_delay -clock clk_sys -max 2.0 [get_ports data_out*]
set_output_delay -clock clk_sys -min 0.5 [get_ports data_out*]

# 时钟不确定性
set_clock_uncertainty -setup 0.2 [get_clocks clk_sys]
set_clock_uncertainty -hold 0.1 [get_clocks clk_sys]

# 伪路径
set_false_path -from [get_pins */rst_n] -to [get_cells *]
```

---

## 7. 验证要求

### 7.1 Lint 检查

| 工具 | 目标 | 警告处理 |
|------|------|----------|
| **SpyGlass Lint** | 0 错误 | 所有警告必须解决或确认 |

```tcl
# SpyGlass Lint 配置
set_project_mode FrontEnd
read_file -format sverilog -top top your_rtl_file.sv
current_design top
read_constraint -format sdc your_constraint.sdc

# 运行 Lint
run_goal lint/lint

# 生成报告
write_report -overwrite report.rpt
```

### 7.2 CDC 检查

| 工具 | 目标 | 违例处理 |
|------|------|----------|
| **SpyGlass CDC** | 0 违例 | 所有违例必须解决或确认 |

```tcl
# SpyGlass CDC 配置
set_project_mode cdc
read_file -format sverilog -top top your_rtl_file.sv
current_design top

# 运行 CDC 检查
run_goal cdc/cdc_setup
run_goal cdc/cdc_hold

# 生成报告
write_report -overwrite cdc_report.rpt
```

### 7.3 代码覆盖率目标

| 覆盖率类型 | 目标值 |
|------------|--------|
| **行覆盖率** | ≥ 95% |
| **分支覆盖率** | ≥ 90% |
| **条件覆盖率** | ≥ 85% |
| **FSM 覆盖率** | 100% |
| **Toggle 覆盖率** | ≥ 90% |

---

## 8. 提交规范

### 8.1 Git 提交规范

```
# 提交信息格式
<type>(<scope>): <subject>

<body>

<footer>
```

| 类型 | 说明 |
|------|------|
| **feat** | 新功能 |
| **fix** | Bug 修复 |
| **refactor** | 代码重构 |
| **style** | 代码风格调整 |
| **docs** | 文档更新 |
| **test** | 测试代码 |

### 8.2 代码审查清单

- [ ] 代码符合编码规范
- [ ] 所有参数有默认值
- [ ] 所有信号已声明
- [ ] 所有时钟域已明确
- [ ] 所有复位已处理
- [ ] 无时序违例风险
- [ ] 无组合逻辑环路
- [ ] 无锁存器
- [ ] 注释充分
- [ ] 测试覆盖完整

---

## 9. 模块开发流程

### 9.1 开发步骤

```
1. 创建模块框架
   ├── 定义接口
   ├── 定义参数
   └── 创建文件

2. 实现功能逻辑
   ├── 时序逻辑
   ├── 组合逻辑
   └── 输出赋值

3. 单元仿真验证
   ├── 创建测试平台
   ├── 编写测试用例
   └── 验证功能

4. Lint 检查
   ├── 语法检查
   ├── 编码规范检查
   └── 修复问题

5. CDC 检查
   ├── 时钟域检查
   ├── 同步器检查
   └── 修复违例

6. 代码审查
   ├── 同行审查
   ├── 修改反馈
   └── 确认通过

7. 代码提交
   ├── 创建分支
   ├── 提交代码
   └── 合并主干
```

### 9.2 质量门禁

| 阶段 | 通过条件 |
|------|----------|
| **编码完成** | 代码审查通过 |
| **Lint** | 0 错误，0 未确认警告 |
| **CDC** | 0 违例 |
| **仿真** | 100% 测试用例通过 |
| **覆盖率** | ≥ 90% |

---

## 10. 交付物

### 10.1 模块交付清单

| 交付物 | 格式 | 说明 |
|--------|------|------|
| **RTL 代码** | SystemVerilog | 源代码 |
| **仿真文件** | SystemVerilog | 测试平台 |
| **仿真脚本** | Shell/Makefile | 运行脚本 |
| **约束文件** | SDC | 时序约束 |
| **Lint 报告** | PDF | Lint 检查结果 |
| **CDC 报告** | PDF | CDC 检查结果 |
| **仿真报告** | PDF | 仿真验证结果 |
| **覆盖率报告** | HTML | 代码覆盖率 |

---

**文档版本**: V1.0  
**最后更新**: 2026-01-19  
**状态**: 草稿  
**下一步**: 开始 RTL 代码开发

---
*本规范作为 YaoGuang SoC RTL 开发的指导文件。*
