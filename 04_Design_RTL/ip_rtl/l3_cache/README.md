# L3 Cache项目目录结构

```
l3_cache/
├── doc/                          # 文档目录
│   ├── ARCH_SPEC.md              # 架构规格文档
│   ├── TEST_PLAN.md              # 测试计划
│   ├── SIGN_OFF_CHECKLIST.md     # 签核检查清单
│   └── VERIFICATION_REPORT_TEMPLATE.md  # 验证报告模板
│
├── rtl/                          # RTL代码目录
│   ├── l3_cache_define.svh       # 定义文件
│   ├── l3_cache_top.sv           # 顶层模块
│   ├── l3_tag_array.sv           # Tag Array
│   ├── l3_data_array.sv          # Data Array
│   ├── l3_mshr.sv                # MSHR
│   ├── l3_plru.sv                # PLRU替换策略
│   ├── l3_request_handler.sv     # 请求处理器
│   └── l3_cache.f                # 文件列表
│
├── tb/                           # 验证目录
│   ├── l3_cache_intf.sv          # 验证接口
│   ├── l3_cache_config.sv        # 配置类
│   ├── l3_cache_seq_item.sv      # 事务项
│   ├── l3_cache_driver.sv        # 驱动
│   ├── l3_cache_monitor.sv       # 监视器
│   ├── l3_cache_sequencer.sv     # 序列器
│   ├── l3_cache_agent.sv         # Agent
│   ├── l3_cache_scoreboard.sv    # 记分板
│   ├── l3_cache_reference_model.sv  # 参考模型
│   ├── l3_cache_coverage.sv      # 覆盖率
│   ├── l3_cache_virtual_sequencer.sv  # 虚拟序列器
│   ├── l3_cache_base_sequence.sv # 基础序列
│   ├── l3_cache_main_sequence.sv # 主测试序列
│   ├── l3_cache_env.sv           # 验证环境
│   ├── l3_cache_base_test.sv     # 基础测试
│   ├── l3_cache_regression_test.sv  # 回归测试
│   └── l3_cache_tb.f             # 文件列表
│
├── sdc/                          # 时序约束目录
│   ├── l3_cache.sdc              # SDC约束文件
│   └── l3_cache_syn.tcl          # 综合脚本
│
├── waves/                        # 波形目录
│   └── README.md                 # 波形说明
│
├── outputs/                      # 输出目录
│   └── README.md                 # 输出说明
│
├── reports/                      # 报告目录
│   └── README.md                 # 报告说明
│
├── DESIGN_GUIDE.md               # 设计指南
└── README.md                     # 项目说明
```

## 文件说明

| 文件类型 | 描述 |
|---------|------|
| *.sv / *.svh | SystemVerilog RTL和验证代码 |
| *.sdc | Synopsys Design Constraints时序约束 |
| *.tcl | Tcl脚本（综合脚本） |
| *.f | 文件列表（编译顺序） |
| *.md | Markdown文档 |

## 使用说明

### 编译RTL

```bash
vcs -f rtl/l3_cache.f -full64 +v2k
```

### 运行测试

```bash
vcs -f tb/l3_cache_tb.f -full64 +v2k +UVM_TESTNAME=l3_cache_base_test
```

### 查看覆盖率

```urg -dir cov_report/*
```

---

**最后更新**: 2026-01-18
