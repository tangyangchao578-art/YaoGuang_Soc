# UVM验证方法论

## UVM架构

### 验证层次

```
┌─────────────────────────────────────────┐
│         Testbench (顶层)             │
│  ┌────────────────────────────┐   │
│  │     Environment       │   │
│  │  ┌────────────────┐  │   │
│  │  │ Sequencer  │  │   │
│  │  └────────────────┘  │   │
│  └────────────────────────────┘   │
│                                  │
│  ┌────────────────────────────┐  │
│  │       DUT (待测设计)   │  │
│  └────────────────────────────┘  │
│                                  │
│  ┌────────────────────────────┐  │
│  │     Agent (激励驱动)  │  │
│  └────────────────────────────┘  │
│                                  │
│  ┌────────────────────────────┐  │
│  │     Scoreboard (比较)  │  │
│  └────────────────────────────┘  │
│                                  │
│  ┌────────────────────────────┐  │
│  │      Monitor (监控)     │  │
│  └────────────────────────────┘  │
│                                  │
│  ┌────────────────────────────┐  │
│  │    Coverage Collector     │  │
│  └────────────────────────────┘  │
└───────────────────────────────────┘
```

### 核心组件职责

| 组件 | 职责 | 关键方法 |
|--------|------|----------|
| Driver | 生成激励 | run_phase, build_phase |
| Monitor | 监视DUT | extract_phase, sample_phase |
| Scoreboard | 比较结果 | compare_phase, report_phase |
| Sequencer | 协调序列 | run_phase, body_phase |
| Agent | 激励管理 | start_of_simulation_phase |
| Coverage | 覆盖率收集 | report_phase, sample_phase |
| ConfigDB | 配置管理 | 随机配置 |

## 验证流程

### 1. Build Phase

**任务**：构建测试平台

**步骤：**
1. 实例化uvm_test
2. 连接DUT接口
3. 创建uvm_env环境
4. 注册所有组件到factory
5. 配置uvm_config_db

**代码示例：**
```systemverilog
function void build_phase(uvm_phase phase);
  dut_if = my_dut::type_id::get();
  env = my_env::type_id::create("dut_if");

  // 设置虚拟接口
  env.dut = dut_if;

  // 设置虚拟序列
  uvm_config_db::set(uvm_config_db::default_seq, 
                  "virtual_seq", 
                  base_seq::type_id::get());

  uvm_report_info(get_full_name(), "Build phase complete");
endfunction
```

### 2. Connect Phase

**任务**：连接DUT和Testbench

**步骤：**
1. 连接时钟和复位
2. 连接DUT信号到Testbench
3. 连接激励驱动器
4. 连接监视器

**代码示例：**
```systemverilog
initial begin
  // 时钟连接
  dut.clk <= clk;
  dut.rst_n <= rst_n;

  // 信号连接
  write_data <= 32'h0;
  write_valid <= 1'b0;
end
```

### 3. Run Phase

**任务**：执行测试

**步骤：**
1. 设置虚拟序列
2. 启动默认序列
3. 运行到最大时间或事务数量
4. 报告覆盖率

**代码示例：**
```systemverilog
task run_phase(uvm_phase phase);
  uvm_sequence_base_seq seq;
  seq = my_seq::type_id::create();

  if (!$cast(config_db, uvm_object_wrapper, "seq")) begin
    uvm_report_fatal(get_full_name(), "No sequence set");
  end

  phase.raise_objection(this, get_full_name(), "run_phase");
  seq.start(this);
  seq.wait_for_sequence_state_on(uvm_active::IDLE);
  phase.drop_objection(this);
endtask
```

### 4. Check Phase

**任务**：检查结果

**步骤：**
1. 检查Scoreboard错误
2. 验证所有测试通过
3. 检查覆盖率
4. 生成测试报告

**代码示例：**
```systemverilog
function void check_phase(uvm_phase phase);
  int num_errors;
  int num_tests;

  // 统计错误和测试数
  num_errors = sb.error_count;
  num_tests = sb.get_num_items();

  if (num_errors > 0) begin
    uvm_report_error(get_full_name(), 
                  $sformatf("%0d tests failed", num_errors));
  end

  uvm_report_info(get_full_name(), "Check phase complete");
endfunction
```

## 覆盖率驱动验证（CDV）

### 覆盖率模型

**CDV流程：**
1. **功能验证**: 确保所有功能工作
2. **覆盖率采样**: 系统地收集覆盖率
3. **覆盖率分析**: 识别未覆盖代码
4. **定向测试**: 针对未覆盖区域
5. **迭代改进**: 重复以上步骤

### 覆盖率组

**代码覆盖率：**
- **行覆盖率**: 所有可执行行
- **分支覆盖率**: 所有分支语句
- **条件覆盖率**: 所有条件表达式
- **翻转覆盖率**: 所有翻转逻辑
- **路径覆盖率**: 所有控制流路径
- **表达式覆盖率**: 所有表达式

**功能覆盖率：**
- **功能点**: 设计功能
- **事务类型**: 协议操作类型
- **配置组合**: 参数组合
- **状态机**: 状态转换
- **场景**: 典型使用场景

### 覆盖率分析

**分析维度：**
1. **按模块**: 每个模块的覆盖率
2. **按功能**: 每个功能的覆盖率
3. **按场景**: 每个使用场景的覆盖率
4. **按约束**: 不同参数配置的覆盖率

**覆盖率提升策略：**
- **随机化约束**: 增加随机性
- **加权随机**: 优先测试高价值场景
- **覆盖率交叉**: 测试模块间交互
- **边界测试**: 专门测试边界值

## 验证计划

### 测试计划结构

**关键要素：**
- **测试范围**: 包含和不包含的功能
- **测试策略**: 如何达到覆盖率目标
- **资源需求**: 计算服务器、工具许可
- **进度计划**: 阶段和里程碑
- **风险管理**: 可能的阻塞和缓解措施

### 测试用例定义

**用例要素：**
- **测试ID**: 唯一标识符
- **测试名称**: 描述性名称
- **测试描述**: 测试什么功能
- **前置条件**: 测试前要求
- **测试步骤**: 详细操作步骤
- **预期结果**: DUT应如何响应
- **验证方法**: 如何验证结果
- **覆盖率贡献**: 覆盖的代码或功能

### 测试类型分类

| 类型 | 描述 | 示例 |
|------|------|------|
| 功能测试 | 验证正常功能 | 正确读写数据 |
| 边界测试 | 测试边界条件 | 最小/最大值测试 |
| 异常测试 | 测试错误处理 | 非法操作、错误码 |
| 性能测试 | 测试性能指标 | 吞吐量、延迟 |
| 压力测试 | 高负载长时间测试 | 满负载运行 |
| 随机测试 | 随机激励测试 | 随机地址、数据 |
| 回归测试 | 多版本综合验证 | 修复后回归 |
