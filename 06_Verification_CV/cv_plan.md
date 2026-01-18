# YaoGuang SoC 系统级验证计划 (CV Plan)

| 文档版本 | V1.0 |
|---------|------|
| 创建日期 | 2026-01-18 |
| 状态 | 进行中 |
| 负责人 | CV 验证工程师 |

---

## 1. 验证概述

### 1.1 项目背景
- **项目名称**: 摇光(YaoGuang) 车规级 SoC 芯片
- **验证阶段**: 系统级验证 (CV)
- **验证周期**: 2026-12-01 至 2027-01-31 (2个月)
- **里程碑**: M6 - CV 验证通过 (2027-01-31)

### 1.2 验证目标
- 验证 SoC 顶层集成正确性
- 验证完整 Boot 流程
- 验证 OS (Linux/RTOS) 启动
- 验证所有外设功能
- 验证系统性能指标
- 验证 FPGA 原型功能

### 1.3 验证范围

| 验证类型 | 范围 | 优先级 |
|----------|------|--------|
| **SoC 顶层集成** | 时钟、复位、电源域、地址映射 | P0 |
| **Boot 流程** | Boot ROM、BL2、U-Boot、SPL | P0 |
| **内存初始化** | DDR 控制器、LPDDR5 初始化 | P0 |
| **OS 启动** | Linux 内核、Device Tree、驱动 | P0 |
| **外设功能** | PCIe/Ethernet/USB/CAN 等 | P1 |
| **性能验证** | 带宽、延迟、吞吐量 | P1 |
| **压力测试** | 长时间运行、并发测试 | P2 |
| **兼容性测试** | 外设兼容性、软件栈兼容 | P2 |

### 1.4 验证里程碑

| 里程碑 | 日期 | 交付物 | 状态 |
|--------|------|--------|------|
| M6.1 CV 环境就绪 | 2026-12-15 | FPGA/Emulation 环境 | 进行中 |
| M6.2 Boot 验证完成 | 2026-12-31 | Boot 测试报告 | 待开始 |
| M6.3 OS 启动完成 | 2027-01-15 | OS 启动报告 | 待开始 |
| M6.4 外设验证完成 | 2027-01-25 | 外设测试报告 | 待开始 |
| **M6 CV 验证通过** | **2027-01-31** | **最终验证报告** | **待开始** |

---

## 2. 验证环境架构

### 2.1 验证平台

| 平台 | 用途 | 说明 |
|------|------|------|
| **RTL 仿真** | 功能验证 | VCS/Xcelium, 支持 C Test |
| **FPGA 原型** | 快速原型 | Xilinx Versal ACAP |
| **Emulation** | 性能验证 | Palladium/Zebu |
| **硬件测试** | 硅前验证 | 评估板测试 |

### 2.2 验证环境结构

```
06_Verification_CV/
├── cv_plan.md                          # 本验证计划
├── testbench/                          # SystemVerilog Testbench
│   ├── soc_top_tb/                     # SoC 顶层 Testbench
│   │   ├── soc_top_env.sv              # 验证环境
│   │   ├── soc_top_scoreboard.sv       # 记分板
│   │   ├── soc_top_coverage.sv         # 覆盖率
│   │   └── soc_top_if.sv               # 接口定义
│   │
│   ├── c_test_wrapper.sv               # C Test 封装
│   ├── boot_wrapper.sv                 # Boot 流程封装
│   └── axi4_mem_model.sv               # 内存模型
│
├── c_tests/                            # C 语言测试用例
│   ├── boot/                           # Boot 测试
│   │   ├── test_boot_rom.c             # Boot ROM 测试
│   │   ├── test_ddr_init.c             # DDR 初始化测试
│   │   ├── test_boot_progress.c        # Boot 进度测试
│   │   └── test_boot_fail_recovery.c   # Boot 失败恢复
│   │
│   ├── ddr/                            # DDR 测试
│   │   ├── test_ddr_basic.c            # DDR 基础读写
│   │   ├── test_ddr_bandwidth.c        # DDR 带宽测试
│   │   ├── test_ddr_stress.c           # DDR 压力测试
│   │   └── test_ddr_ecc.c              # DDR ECC 测试
│   │
│   ├── peripherals/                    # 外设测试
│   │   ├── test_pcie.c                 # PCIe 测试
│   │   ├── test_ethernet.c             # Ethernet 测试
│   │   ├── test_usb.c                  # USB 测试
│   │   ├── test_can.c                  # CAN FD 测试
│   │   ├── test_gpio.c                 # GPIO 测试
│   │   ├── test_i2c.c                  # I2C 测试
│   │   ├── test_spi.c                  # SPI 测试
│   │   └── test_uart.c                 # UART 测试
│   │
│   └── performance/                    # 性能测试
│       ├── test_memory_bandwidth.c     # 内存带宽
│       ├── test_cpu_performance.c      # CPU 性能
│       ├── test_npu_performance.c      # NPU 性能
│       └── test_noc_performance.c      # NoC 性能
│
├── fpga/                               # FPGA 原型验证
│   ├── versal_acap/                    # Xilinx Versal ACAP
│   │   ├── Makefile                    # 编译脚本
│   │   ├── top.xpr                     # Vivado 项目
│   │   ├── bitstream.tcl               # 比特流生成
│   │   └── debug.tcl                   # 调试配置
│   │
│   ├── constraints/                    # 约束文件
│   │   ├── timing.xdc                  # 时序约束
│   │   ├── io.xdc                      # IO 约束
│   │   └── config.xdc                  # 配置约束
│   │
│   └── scripts/                        # FPGA 脚本
│       ├── build_fpga.sh               # FPGA 编译
│       ├── program_fpga.sh             # FPGA 烧录
│       └── debug_fpga.sh               # FPGA 调试
│
├── emulation/                          # Emulation 验证
│   ├── palladium/                      # Cadence Palladium
│   │   ├── compile.tcl                 # 编译脚本
│   │   ├── emulation.tcl               # Emulation 脚本
│   │   └── mapping.tcl                 # RTL 映射
│   │
│   ├── zebu/                           # Synopsys Zebu
│   │   ├── compile.tcl                 # 编译脚本
│   │   ├── emulation.tcl               # Emulation 脚本
│   │   └── mapping.tcl                 # RTL 映射
│   │
│   └── scripts/                        # Emulation 脚本
│       ├── run_emulation.py            # 运行 Emulation
│       ├── collect_results.py          # 收集结果
│       └── performance_analysis.py     # 性能分析
│
├── regression/                         # 回归测试
│   ├── cv_regression.yaml              # CV 回归配置
│   ├── cv_test_list.yaml               # 测试用例清单
│   ├── run_cv_regression.sh            # 运行回归
│   └── cv_report_template.md           # 报告模板
│
├── coverage_reports/                   # 覆盖率报告
│   ├── cv_coverage_summary.md          # 覆盖率汇总
│   └── coverage_trends.md              # 覆盖率趋势
│
└── docs/                               # 文档
    ├── cv_testplan.md                  # 详细测试计划
    ├── cv_user_guide.md                # 使用指南
    └── cv_debug_guide.md               # 调试指南
```

---

## 3. 详细验证计划

### 3.1 SoC 顶层集成验证

#### 3.1.1 时钟系统验证

| 测试项 | 描述 | 优先级 | 验收标准 |
|--------|------|--------|----------|
| CLK-001 | 主PLL锁定 | P0 | PLL锁定信号有效 |
| CLK-002 | 各时钟域频率 | P0 | clk_core=2GHz, clk_npu=2GHz |
| CLK-003 | 时钟切换 | P0 | 无毛刺切换 |
| CLK-004 | 时钟门控 | P1 | 门控信号正确 |
| CLK-005 | 时钟监控 | P1 | 频率异常检测 |

#### 3.1.2 复位系统验证

| 测试项 | 描述 | 优先级 | 验收标准 |
|--------|------|--------|----------|
| RST-001 | POR复位 | P0 | 上电复位正确 |
| RST-002 | 软复位 | P0 | 软件复位正确 |
| RST-003 | 复位去抖 | P0 | 无毛刺 |
| RST-004 | 复位释放顺序 | P0 | 按序释放 |
| RST-005 | 看门狗复位 | P0 | 超时复位 |

#### 3.1.3 电源域验证

| 测试项 | 描述 | 优先级 | 验收标准 |
|--------|------|--------|----------|
| PWR-001 | 电源域上电 | P0 | 上电时序正确 |
| PWR-002 | 电源域下电 | P0 | 下电时序正确 |
| PWR-003 | 电源状态切换 | P0 | 状态机正确 |
| PWR-004 | 隔离单元 | P0 | 隔离正确 |
| PWR-005 | 保留寄存器 | P1 | 数据保持 |

#### 3.1.4 地址映射验证

| 测试项 | 描述 | 优先级 | 验收标准 |
|--------|------|--------|----------|
| ADDR-001 | 地址解码 | P0 | 正确路由到从设备 |
| ADDR-002 | 非法地址访问 | P0 | 返回错误响应 |
| ADDR-003 | 地址对齐 | P1 | 对齐检查正确 |
| ADDR-004 | 内存保护 | P1 | 权限检查正确 |

### 3.2 Boot 流程验证

#### 3.2.1 Boot ROM 验证

| 测试项 | 描述 | 优先级 | 验收标准 |
|--------|------|--------|----------|
| BOOT-001 | Boot ROM 读取 | P0 | 正确读取启动代码 |
| BOOT-002 | Boot ROM 校验 | P0 | CRC 校验通过 |
| BOOT-003 | Boot 模式选择 | P0 | 模式正确识别 |
| BOOT-004 | 启动介质选择 | P0 | 正确切换介质 |

#### 3.2.2 DDR 初始化验证

| 测试项 | 描述 | 优先级 | 验收标准 |
|--------|------|--------|----------|
| DDR-001 | DDR 控制器初始化 | P0 | 初始化序列正确 |
| DDR-002 | DDR 训练 | P0 | 训练通过 |
| DDR-003 | DDR 读写测试 | P0 | 读写正确 |
| DDR-004 | DDR 带宽测试 | P1 | 达到目标带宽 |
| DDR-005 | DDR ECC 验证 | P0 | ECC 正确工作 |

#### 3.2.3 Bootloader 验证

| 测试项 | 描述 | 优先级 | 验收标准 |
|--------|------|--------|----------|
| BL-001 | BL2 启动 | P0 | BL2 正常执行 |
| BL-002 | 设备树传递 | P0 | 设备树正确 |
| BL-003 | 负载 Linux | P0 | Linux 正确加载 |
| BL-004 | 启动参数 | P0 | 参数正确传递 |

### 3.3 OS 启动验证

#### 3.3.1 Linux 启动验证

| 测试项 | 描述 | 优先级 | 验收标准 |
|--------|------|--------|----------|
| LINUX-001 | Linux 内核解压 | P0 | 解压成功 |
| LINUX-002 | 设备树解析 | P0 | 解析正确 |
| LINUX-003 | 驱动初始化 | P0 | 主要驱动加载 |
| LINUX-004 | Rootfs 挂载 | P0 | 挂载成功 |
| LINUX-005 | 用户空间启动 | P0 | init 进程运行 |
| LINUX-006 | 网络功能 | P1 | 网络正常工作 |

#### 3.3.2 RTOS 启动验证 (可选)

| 测试项 | 描述 | 优先级 | 验收标准 |
|--------|------|--------|----------|
| RTOS-001 | RTOS 内核启动 | P0 | 内核运行 |
| RTOS-002 | 任务调度 | P0 | 调度正常 |
| RTOS-003 | 中断处理 | P0 | 中断正确 |
| RTOS-004 | 内存管理 | P1 | 内存正确 |

### 3.4 外设功能验证

#### 3.4.1 PCIe 验证

| 测试项 | 描述 | 优先级 | 验收标准 |
|--------|------|--------|----------|
| PCIE-001 | 链路训练 | P0 | 训练成功 |
| PCIE-002 | 枚举检测 | P0 | 设备检测 |
| PCIE-003 | DMA 传输 | P0 | DMA 正确 |
| PCIE-004 | 中断测试 | P0 | 中断正确 |

#### 3.4.2 Ethernet 验证

| 测试项 | 描述 | 优先级 | 验收标准 |
|--------|------|--------|----------|
| ETH-001 | MAC 初始化 | P0 | 初始化成功 |
| ETH-002 | 帧收发测试 | P0 | 收发正确 |
| ETH-003 | 速率协商 | P0 | 速率正确 |
| ETH-004 | DMA 传输 | P0 | DMA 正确 |

#### 3.4.3 USB 验证

| 测试项 | 描述 | 优先级 | 验收标准 |
|--------|------|--------|----------|
| USB-001 | 设备枚举 | P0 | 枚举成功 |
| USB-002 | 数据传输 | P0 | 传输正确 |
| USB-003 | 中断处理 | P0 | 中断正确 |
| USB-004 | 电源管理 | P1 | 电源管理 |

#### 3.4.4 其他外设

| 测试项 | 描述 | 优先级 | 验收标准 |
|--------|------|--------|----------|
| CAN-001 | CAN 收发测试 | P1 | 收发正确 |
| GPIO-001 | GPIO 读写 | P1 | 读写正确 |
| I2C-001 | I2C 读写 | P1 | 读写正确 |
| SPI-001 | SPI 传输 | P1 | 传输正确 |
| UART-001 | UART 收发 | P1 | 收发正确 |

### 3.5 性能验证

| 测试项 | 描述 | 优先级 | 验收标准 |
|--------|------|--------|----------|
| PERF-001 | CPU 性能 | P1 | Dhrystone ≥ X DMIPS/MHz |
| PERF-002 | NPU 性能 | P1 | TOPS ≥ 300 TOPS |
| PERF-003 | DDR 带宽 | P1 | ≥ 100 GB/s |
| PERF-004 | NoC 带宽 | P1 | ≥ 2 TB/s |
| PERF-005 | 启动时间 | P1 | Boot < 100ms |

---

## 4. 测试用例列表

### 4.1 C Test 用例

| 序号 | 测试用例 | 类型 | 优先级 | 对应需求 |
|------|----------|------|--------|----------|
| 1 | test_boot_rom | 功能 | P0 | BOOT-001 |
| 2 | test_ddr_init | 功能 | P0 | DDR-001 |
| 3 | test_ddr_basic_rw | 功能 | P0 | DDR-003 |
| 4 | test_ddr_bandwidth | 性能 | P1 | DDR-004 |
| 5 | test_ddr_ecc | 功能 | P0 | DDR-005 |
| 6 | test_pcie_link | 功能 | P0 | PCIE-001 |
| 7 | test_pcie_enum | 功能 | P0 | PCIE-002 |
| 8 | test_pcie_dma | 功能 | P0 | PCIE-003 |
| 9 | test_eth_mac | 功能 | P0 | ETH-001 |
| 10 | test_eth_frame | 功能 | P0 | ETH-002 |
| 11 | test_usb_enum | 功能 | P0 | USB-001 |
| 12 | test_usb_transfer | 功能 | P0 | USB-002 |
| 13 | test_can_fd | 功能 | P1 | CAN-001 |
| 14 | test_gpio_basic | 功能 | P1 | GPIO-001 |
| 15 | test_i2c_eeprom | 功能 | P1 | I2C-001 |
| 16 | test_spi_flash | 功能 | P1 | SPI-001 |
| 17 | test_uart_loopback | 功能 | P1 | UART-001 |
| 18 | test_cpu_coremark | 性能 | P1 | PERF-001 |
| 19 | test_npu_inference | 性能 | P1 | PERF-002 |
| 20 | test_noc_bandwidth | 性能 | P1 | PERF-004 |

### 4.2 仿真测试用例

| 序号 | 测试用例 | 类型 | 优先级 | 对应需求 |
|------|----------|------|--------|----------|
| 21 | sim_clk_rst | 功能 | P0 | CLK-001, RST-001 |
| 22 | sim_power_domain | 功能 | P0 | PWR-001 |
| 23 | sim_address_map | 功能 | P0 | ADDR-001 |
| 24 | sim_boot_full | 功能 | P0 | BOOT-001~004 |
| 25 | sim_linux_start | 功能 | P0 | LINUX-001~006 |
| 26 | sim_rtos_start | 功能 | P1 | RTOS-001~004 |
| 27 | sim_pcie_stress | 压力 | P2 | PCIE-ALL |
| 28 | sim_eth_stress | 压力 | P2 | ETH-ALL |
| 29 | sim_usb_stress | 压力 | P2 | USB-ALL |
| 30 | sim_performance_full | 性能 | P1 | PERF-001~005 |

---

## 5. 验证环境配置

### 5.1 RTL 仿真配置

| 配置项 | 值 |
|--------|------|
| 仿真器 | VCS 2023.12 / Xcelium |
| 编译选项 | -sverilog -full64 +v2k |
| 仿真选项 | -ucli -do run.do |
| 覆盖率 | line+branch+cond+toggle+fsm+assert |

### 5.2 FPGA 原型配置

| 配置项 | 值 |
|--------|------|
| FPGA 平台 | Xilinx Versal ACAP |
| 器件 | XCV1902 |
| 综合工具 | Vivado 2023.2 |
| 目标频率 | 100 MHz (初始) |
| 调试工具 | ChipScope ILA |

### 5.3 Emulation 配置

| 配置项 | 值 |
|--------|------|
| Emulator | Palladium Z1 / Zebu Z4 |
| 编译时间 | ~4-8 小时 |
| 运行速度 | ~100-500 kHz |
| 内存需求 | 256 GB |

---

## 6. 回归测试策略

### 6.1 回归级别

| 级别 | 运行频率 | 测试数 | 执行时间 | 通过率 |
|------|----------|--------|----------|--------|
| **Sanity** | 每次提交 | 20 | < 10分钟 | 100% |
| **Daily** | 每日 | 50 | < 1小时 | 95% |
| **Weekly** | 每周 | 100 | < 4小时 | 90% |
| **Full** | 发布前 | 200 | < 12小时 | 85% |

### 6.2 回归配置

```yaml
regression_suites:
  sanity:
    description: "快速冒烟测试，验证基本功能"
    priority: P0
    timeout: 600  # 10分钟
    parallel_jobs: 4
    pass_threshold: 100.0
    tests:
      - test_boot_rom
      - test_ddr_init
      - test_ddr_basic_rw
      - test_pcie_link
      - test_eth_mac
      - test_usb_enum
      - sim_clk_rst
      - sim_power_domain
      - sim_address_map

  daily:
    description: "每日回归测试"
    priority: P0
    timeout: 3600  # 1小时
    parallel_jobs: 8
    pass_threshold: 95.0
    tests:
      - "*"  # 所有P0测试

  weekly:
    description: "每周完整回归"
    priority: P1
    timeout: 14400  # 4小时
    parallel_jobs: 16
    pass_threshold: 90.0
    tests:
      - "*"  # 所有测试

  full:
    description: "发布前完整回归"
    priority: P2
    timeout: 43200  # 12小时
    parallel_jobs: 32
    pass_threshold: 85.0
    tests:
      - "*"  # 所有测试
```

---

## 7. 覆盖率要求

### 7.1 代码覆盖率目标

| 覆盖率类型 | 目标 |
|------------|------|
| 行覆盖率 | ≥ 90% |
| 分支覆盖率 | ≥ 85% |
| 条件覆盖率 | ≥ 85% |
| 翻转覆盖率 | ≥ 85% |
| 状态机覆盖率 | ≥ 90% |
| 断言覆盖率 | ≥ 85% |

### 7.2 功能覆盖率

| 验证项 | 目标 |
|--------|------|
| Boot 流程覆盖率 | 100% |
| 外设功能覆盖率 | 100% |
| 性能指标覆盖率 | 100% |

---

## 8. 缺陷管理

### 8.1 缺陷严重级别

| 级别 | 描述 | 响应时间 |
|------|------|----------|
| P1 (Blocker) | 阻塞验证 | 4小时 |
| P2 (Critical) | 功能严重错误 | 24小时 |
| P3 (Major) | 功能错误 | 1周 |
| P4 (Minor) | 小问题 | 2周 |

### 8.2 缺陷目标

| 指标 | 目标 |
|------|------|
| 缺陷修复率 | ≥ 98% |
| 缺陷逃逸率 | ≤ 2% |
| 验证缺陷密度 | ≤ 0.5/KLOC |

---

## 9. 资源需求

### 9.1 人力资源

| 角色 | 人数 | 职责 |
|------|------|------|
| CV 验证工程师 | 3 | 验证计划、执行 |
| FPGA 工程师 | 2 | FPGA 原型搭建 |
| Emulation 工程师 | 1 | Emulation 环境 |
| 软件工程师 | 2 | C Test 开发 |
| 验证架构师 | 1 | 环境架构 |

### 9.2 计算资源

| 资源 | 需求 |
|------|------|
| 仿真服务器 | 50 核 |
| FPGA 开发板 | 2 套 |
| Emulator | 1 台 |
| 存储空间 | 10 TB |

---

## 10. 风险与应对

| 风险 | 概率 | 影响 | 应对措施 |
|------|------|------|----------|
| FPGA 资源不足 | 中 | 高 | 优化 RTL、资源评估 |
| DDR 初始化问题 | 中 | 高 | 提前 DDR 验证 |
| Linux 启动失败 | 中 | 高 | 多种 Boot 模式支持 |
| 性能不达标 | 低 | 中 | 提前性能分析 |
| 工具链问题 | 低 | 中 | 备用工具准备 |

---

## 11. 交付物清单

| 交付物 | 说明 | 状态 |
|--------|------|------|
| CV 验证计划 | 本文档 | 已交付 |
| C Test 用例 | 20+ 测试用例 | 进行中 |
| FPGA 原型环境 | Versal ACAP 环境 | 进行中 |
| Emulation 环境 | Palladium/Zebu 环境 | 进行中 |
| 回归测试套件 | 200+ 测试用例 | 进行中 |
| 覆盖率报告 | 各阶段覆盖率报告 | 待交付 |
| CV 验证报告 | 最终验证报告 | 待交付 |

---

## 12. 审批

| 角色 | 姓名 | 签名 | 日期 |
|------|------|------|------|
| CV 验证工程师 | - | - | - |
| 验证经理 | - | - | - |
| 架构师 | - | - | - |
| 项目经理 | - | - | - |

---

**文档版本**: V1.0
**创建日期**: 2026-01-18
**最后更新**: 2026-01-18
**状态**: 初稿
