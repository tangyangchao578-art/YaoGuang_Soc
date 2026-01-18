# FPGA原型验证工作流程

## 验证阶段划分

### 1. RTL准备阶段

**任务清单：**
- [ ] 检查RTL代码可综合性
- [ ] 添加FPGA特定的综合约束
- [ ] 验证时钟和复位策略
- [ ] 确认状态机编码方式
- [ ] 检查异步逻辑和latch

**检查工具：**
- `lint_check`: 综合前代码检查
- `synth_check`: 综合约束检查

### 2. 综合阶段

**任务清单：**
- [ ] 设置综合策略（性能/资源/功耗）
- [ ] 应用时序约束
- [ ] 执行综合
- [ ] 分析综合报告
- [ ] 优化综合结果

**关键命令：**
```tcl
synth_design -top top -part xc7k325tffg900-2
report_utilization -file utilization.txt
report_timing_summary -file timing.txt
```

### 3. 布局布线阶段

**任务清单：**
- [ ] 执行布局布线
- [ ] 检查时序违例
- [ ] 优化时序
- [ ] 分析资源使用
- [ ] 生成bitstream

**时序收敛流程：**
1. 分析时序报告
2. 识别关键路径
3. 应用优化策略
4. 重新运行布局布线
5. 验证时序改善

### 4. 原型验证阶段

**任务清单：**
- [ ] 配置调试工具（ILA/SignalTap）
- [ ] 加载bitstream到FPGA
- [ ] 运行测试用例
- [ ] 收集调试波形
- [ ] 分析测试结果

### 5. 回归测试阶段

**任务清单：**
- [ ] 准备回归测试集
- [ ] 自动化测试执行
- [ ] 收集测试结果
- [ ] 生成测试报告
- [ ] 分析失败用例

## 常用命令参考

### Vivado常用命令

```tcl
# 项目管理
create_project project_name ./project -part xc7k325tffg900-2
add_files -norecurse {file1.v file2.v}
import_files -fileset constrs_1 -force constraints.xdc

# 综合
synth_design -top top -part xc7k325tffg900-2
opt_design
power_opt_design

# 布局布线
place_design
phys_opt_design
route_design

# 报告
report_utilization
report_timing_summary
report_clock_interaction
report_drc

# 下载
open_hw_manager
connect_hw_server
open_hw_target
current_hw_device [get_hw_devices xc7k325t]
program_hw_devices [current_hw_device]

# ILA配置
create_debug_core u_ila_0 ila
set_property C_DATA_DEPTH 1024 [get_debug_cores u_ila_0]
set_property C_TRIG_IN_COUNT 1 [get_debug_cores u_ila_0]
```

### Quartus常用命令

```tcl
# 项目创建
project_new my_project -overwrite
set_global_assignment -name FAMILY "Cyclone V"
set_global_assignment -name DEVICE 5CGXFC7C7F23C8
set_global_assignment -name TOP_LEVEL_ENTITY top

# 添加文件
set_global_assignment -name VERILOG_FILE file1.v
set_global_assignment -name VERILOG_FILE file2.v
set_global_assignment -name SDC_FILE constraints.sdc

# 分析与综合
execute_flow -analysis_and_elaboration
execute_flow -synthesis

# 布局布线
execute_flow -fit
execute_flow -assemble

# 报告
report_resources -type all
report_timing -setup
report_timing -hold
report_utilization

# SignalTap
set_global_assignment -name SIGNALTAP_FILE stp1.stp
```

## 调试技巧

### ILA触发设置

**简单触发：**
```tcl
# 单个信号触发
set_property TRIGGER_VALUE 1 [get_hw_probe_values -of_objects [get_hw_probes u_ila_0/trigger0]]
```

**组合触发：**
```tcl
# 多信号组合触发
set_property TRIGGER_CONDITION "[probe0] == 1 && [probe1] == 0" [get_hw_debug_cores u_ila_0]
```

**序列触发：**
```tcl
# 事件序列触发
set_property TRIGGER_CONDITION "seq: [probe0] -> [probe1]" [get_hw_debug_cores u_ila_0]
```

### 波形分析

**时间戳分析：**
1. 记录事件发生时间
2. 计算事件间时间差
3. 分析时序关系

**协议解码：**
1. 捕获总线信号
2. 应用协议解码器
3. 解析协议内容

## 性能优化

### 时序优化

**流水线插入：**
```verilog
// 优化前
assign result = a * b + c * d;

// 优化后 - 插入寄存器
reg [31:0] mult1, mult2;
always @(posedge clk) begin
  mult1 <= a * b;
  mult2 <= c * d;
end
assign result = mult1 + mult2;
```

**逻辑复制：**
```verilog
// 优化前 - 高扇出
assign out1 = data;
assign out2 = data;
assign out3 = data;
assign out4 = data;

// 优化后 - 信号复制
assign out1 = data;
assign out2 = data_copy1;
assign out3 = data_copy2;
assign out4 = data_copy3;
```

### 资源优化

**状态机编码：**
```verilog
// 独热码 - 速度快，面积大
typedef enum logic [3:0] {
  IDLE     = 4'b0001,
  READ     = 4'b0010,
  WRITE    = 4'b0100,
  DONE     = 4'b1000
} state_t;

// 二进制编码 - 面积小，速度慢
typedef enum logic [1:0] {
  IDLE     = 2'b00,
  READ     = 2'b01,
  WRITE    = 2'b10,
  DONE     = 2'b11
} state_t;
```

**BRAM使用：**
```verilog
// 分布式RAM - 小容量
reg [7:0] ram [0:15];

// BRAM - 大容量
(* ram_style = "block" *)
reg [31:0] bram [0:1023];
```

## 测试用例设计

### 功能测试

**正常功能测试：**
- 标准操作流程
- 常用配置组合
- 正常数据范围

**边界测试：**
- 最小/最大值
- 溢出/下溢
- 极限条件

**异常测试：**
- 错误注入
- 中断处理
- 异常流程

### 性能测试

**带宽测试：**
```python
# 带宽测试示例
start_time = time.time()
for i in range(1000000):
    write_data(i, 0xDEADBEEF)
end_time = time.time()
bandwidth = (1000000 * 4) / (end_time - start_time)
print(f"Bandwidth: {bandwidth} MB/s")
```

**延迟测试：**
```python
# 延迟测试示例
for i in range(100):
    start_cycle = read_counter()
    write_data(i, 0xDEADBEEF)
    end_cycle = read_counter()
    latency = end_cycle - start_cycle
    print(f"Latency {i}: {latency} cycles")
```

## 问题排查流程

### 综合失败

1. 检查RTL代码语法
2. 查看错误日志
3. 检查约束文件
4. 验证工具版本

### 时序违例

1. 分析时序报告
2. 识别关键路径
3. 应用优化策略
4. 重新布局布线

### 功能错误

1. 检查RTL逻辑
2. 验证测试激励
3. 捕获调试波形
4. 分析错误原因

### 性能不达标

1. 测量实际性能
2. 分析瓶颈
3. 优化设计
4. 重新验证
