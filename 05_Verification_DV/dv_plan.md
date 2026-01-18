# YaoGuang SoC 模块级验证计划 (DV Plan)

| 文档版本 | V1.0 |
|---------|------|
| 创建日期 | 2026-01-18 |
| 最后更新 | 2026-01-18 |
| 状态 | 初稿 |
| 负责人 | DV 验证工程师 |

---

## 1. 验证范围概述

### 1.1 项目背景
- **项目名称**: 摇光(YaoGuang) 车规级 SoC 芯片
- **制程工艺**: TSMC 5nm
- **目标应用**: L3/L4 自动驾驶
- **验证阶段**: 模块级验证 (DV)
- **验证周期**: 2026-05 至 2026-11 (7个月)

### 1.2 验证目标
- 确保所有 RTL 模块功能正确
- 达到代码覆盖率 ≥ 95%
- 达到功能覆盖率 100% (P0特性)
- 满足 ISO 26262 ASIL-D 安全验证要求

### 1.3 验证里程碑

| 里程碑 | 日期 | 交付物 |
|--------|------|--------|
| M5.1 验证环境就绪 | 2026-06-15 | UVM 环境、VIP |
| M5.2 Safety Island Sign-off | 2026-08-31 | 覆盖率报告、验证报告 |
| M5.3 NPU Sign-off | 2026-09-30 | 覆盖率报告、验证报告 |
| M5.4 其他模块 Sign-off | 2026-10-31 | 覆盖率报告、验证报告 |
| M5 DV 验证通过 | 2026-11-30 | 最终验证报告 |

---

## 2. 验证模块列表

### 2.1 模块清单与优先级

| 序号 | 模块名称 | 优先级 | ASIL 等级 | 验证复杂度 | 预估工时 |
|------|----------|--------|-----------|------------|----------|
| 1 | Safety Island | P0 | ASIL-D | 高 | 30人月 |
| 2 | NPU Cluster (4x) | P0 | ASIL-B | 高 | 35人月 |
| 3 | CPU Subsystem | P0 | ASIL-B | 中 | 20人月 |
| 4 | PMU | P0 | ASIL-D | 中 | 15人月 |
| 5 | ISP | P1 | ASIL-B | 中 | 15人月 |
| 6 | Memory Controller | P0 | ASIL-B | 中 | 15人月 |
| 7 | L3 Cache | P1 | ASIL-B | 中 | 10人月 |
| 8 | NoC Interconnect | P0 | ASIL-B | 高 | 20人月 |
| 9 | PCIe Controller | P1 | QM | 中 | 12人月 |
| 10 | Ethernet Controller | P1 | QM | 低 | 8人月 |
| 11 | USB Controller | P1 | QM | 中 | 10人月 |
| 12 | Display Controller | P2 | QM | 中 | 10人月 |
| 13 | Audio Controller | P2 | QM | 低 | 5人月 |
| 14 | CAN FD Controller | P1 | ASIL-B | 低 | 5人月 |
| 15 | I2C/SPI/GPIO | P2 | QM | 低 | 5人月 |
| 16 | Crypto Engine | P1 | ASIL-B | 中 | 8人月 |
| 17 | Debug Subsystem | P2 | QM | 低 | 3人月 |

### 2.2 验证资源分配

| 资源类型 | 数量 | 说明 |
|----------|------|------|
| 验证工程师 | 30人 | DV 阶段峰值 |
| 仿真器 License | 50个 | VCS/Xcelium |
| 硬件资源 | 100+ CPU cores | 回归测试并行 |
| 存储空间 | 10TB | 回归测试日志 |

---

## 3. 详细测试点分解

### 3.1 Safety Island 验证

#### 3.1.1 双核锁步处理器测试

| 测试点 ID | 测试描述 | 优先级 | 测试类型 | 预期结果 |
|-----------|----------|--------|----------|----------|
| SI-TEST-001 | Primary Core 指令执行 | P0 | 功能 | 指令正确执行 |
| SI-TEST-002 | Shadow Core 指令执行 | P0 | 功能 | 指令正确执行 |
| SI-TEST-003 | 结果比较器检测 | P0 | 功能 | 差异被检测 |
| SI-TEST-004 | 错误响应时间 < 5 cycles | P0 | 时序 | 延迟符合规格 |
| SI-TEST-005 | 错误码记录 | P0 | 功能 | 32bit 错误码正确 |
| SI-TEST-006 | 单比特错误检测 100% | P0 | 异常 | 所有单比特错误被检测 |
| SI-TEST-007 | 双比特错误检测 | P0 | 异常 | 双比特错误被检测 |
| SI-TEST-008 | 确定性执行模式 | P1 | 功能 | 执行结果可重复 |
| SI-TEST-009 | 中断延迟测试 | P2 | 性能 | 中断延迟 < 10 cycles |

#### 3.1.2 ECC 内存控制器测试

| 测试点 ID | 测试描述 | 优先级 | 测试类型 | 预期结果 |
|-----------|----------|--------|----------|----------|
| SI-ECC-001 | SECDED 纠错 | P0 | 功能 | 单比特错误纠正 |
| SI-ECC-002 | 双错误检测 | P0 | 异常 | 双比特错误检测 |
| SI-ECC-003 | 校验码生成 | P0 | 功能 | 8-bit ECC 正确 |
| SI-ECC-004 | ECC 错误中断 | P0 | 功能 | 错误触发中断 |
| SI-ECC-005 | 错误计数与日志 | P0 | 功能 | 错误计数正确 |
| SI-ECC-006 | ECC 旁路模式 | P1 | 功能 | 旁路模式可用 |
| SI-ECC-007 | 内存 BIST | P1 | 功能 | BIST 通过 |
| SI-ECC-008 | 读修改写场景 | P0 | 功能 | RMW 场景 ECC 正确 |

#### 3.1.3 看门狗测试

| 测试点 ID | 测试描述 | 优先级 | 测试类型 | 预期结果 |
|-----------|----------|--------|----------|----------|
| SI-WDG-001 | 内部看门狗超时 | P0 | 功能 | 超时触发复位 |
| SI-WDG-002 | 外部看门狗接口 | P0 | 功能 | 外部看门狗响应 |
| SI-WDG-003 | 窗口看门狗 | P0 | 功能 | 窗口内喂狗有效 |
| SI-WDG-004 | 喂狗超时检测 | P0 | 异常 | 超时检测正确 |
| SI-WDG-005 | 失效安全响应 | P0 | 功能 | 安全响应触发 |
| SI-WDG-006 | 独立时钟域 | P0 | 时序 | 独立时钟正确 |
| SI-WDG-007 | 看门狗状态寄存器 | P1 | 功能 | 状态可读 |

#### 3.1.4 故障注入测试

| 测试点 ID | 测试描述 | 优先级 | 测试类型 | 预期结果 |
|-----------|----------|--------|----------|----------|
| SI-FLT-001 | 单比特故障注入 | P0 | 异常 | 故障被检测 |
| SI-FLT-002 | 多比特故障注入 | P0 | 异常 | 故障被检测 |
| SI-FLT-003 | 故障响应验证 | P0 | 功能 | 响应正确 |
| SI-FLT-004 | BIST 模式故障测试 | P1 | 功能 | BIST 检测故障 |
| SI-FLT-005 | 永久故障注入 | P0 | 异常 | 永久故障检测 |

### 3.2 NPU Cluster 验证

#### 3.2.1 张量处理单元测试

| 测试点 ID | 测试描述 | 优先级 | 测试类型 | 预期结果 |
|-----------|----------|--------|----------|----------|
| NPU-TEN-001 | INT8 矩阵乘法 | P0 | 功能 | 结果正确 |
| NPU-TEN-002 | INT16 矩阵乘法 | P0 | 功能 | 结果正确 |
| NPU-TEN-003 | FP16 矩阵乘法 | P0 | 功能 | 结果正确 |
| NPU-TEN-004 | 稀疏矩阵加速 | P1 | 功能 | 稀疏加速生效 |
| NPU-TEN-005 | 量化支持 | P1 | 功能 | 量化正确 |
| NPU-TEN-006 | 动态量化 | P2 | 功能 | 动态量化正确 |

#### 3.2.2 激活单元测试

| 测试点 ID | 测试描述 | 优先级 | 测试类型 | 预期结果 |
|-----------|----------|--------|----------|----------|
| NPU-ACT-001 | ReLU 激活 | P0 | 功能 | 激活正确 |
| NPU-ACT-002 | Sigmoid 激活 | P0 | 功能 | 激活正确 |
| NPU-ACT-003 | Tanh 激活 | P1 | 功能 | 激活正确 |
| NPU-ACT-004 | Leaky ReLU | P1 | 功能 | 激活正确 |

#### 3.2.3 池化单元测试

| 测试点 ID | 测试描述 | 优先级 | 测试类型 | 预期结果 |
|-----------|----------|--------|----------|----------|
| NPU-POOL-001 | Max Pooling | P0 | 功能 | 池化正确 |
| NPU-POOL-002 | Average Pooling | P0 | 功能 | 池化正确 |
| NPU-POOL-003 | Global Pooling | P1 | 功能 | 池化正确 |
| NPU-POOL-004 | 步长测试 | P0 | 功能 | 步长正确 |

#### 3.2.4 数据流测试

| 测试点 ID | 测试描述 | 优先级 | 测试类型 | 预期结果 |
|-----------|----------|--------|----------|----------|
| NPU-DATA-001 | 片上 SRAM 读写 | P0 | 功能 | SRAM 访问正确 |
| NPU-DATA-002 | 数据预取 | P1 | 功能 | 预取命中 |
| NPU-DATA-003 | 数据压缩 | P2 | 功能 | 压缩率正确 |
| NPU-DATA-004 | 跨 Cluster 通信 | P0 | 功能 | 通信正确 |

### 3.3 CPU 子系统验证

#### 3.3.1 Cortex-A78AE 集成测试

| 测试点 ID | 测试描述 | 优先级 | 测试类型 | 预期结果 |
|-----------|----------|--------|----------|----------|
| CPU-A78-001 | 指令执行 | P0 | 功能 | 指令正确执行 |
| CPU-A78-002 | 异常处理 | P0 | 功能 | 异常正确处理 |
| CPU-A78-003 | 中断处理 | P0 | 功能 | 中断正确响应 |
| CPU-A78-004 | Cache 使能 | P0 | 功能 | Cache 正常工作 |
| CPU-A78-005 | MMU 使能 | P0 | 功能 | 地址转换正确 |

#### 3.3.2 Cache 一致性测试

| 测试点 ID | 测试描述 | 优先级 | 测试类型 | 预期结果 |
|-----------|----------|--------|----------|----------|
| CPU-CACHE-001 | L1 Cache 读 | P0 | 功能 | Cache 命中正确 |
| CPU-CACHE-002 | L1 Cache 写 | P0 | 功能 | 写回正确 |
| CPU-CACHE-003 | L2 Cache 一致性 | P0 | 功能 | 一致性维护 |
| CPU-CACHE-004 | Cache 刷新 | P0 | 功能 | 刷新正确 |
| CPU-CACHE-005 | Cache 无效化 | P0 | 功能 | 无效化正确 |

#### 3.3.3 中断控制器测试

| 测试点 ID | 测试描述 | 优先级 | 测试类型 | 预期结果 |
|-----------|----------|--------|----------|----------|
| CPU-GIC-001 | 中断使能/禁止 | P0 | 功能 | 控制正确 |
| CPU-GIC-002 | 中断优先级 | P0 | 功能 | 优先级正确 |
| CPU-GIC-003 | 中断嵌套 | P0 | 功能 | 嵌套正确 |
| CPU-GIC-004 | SGI 产生 | P0 | 功能 | SGI 正确 |
| CPU-GIC-005 | PPI 处理 | P0 | 功能 | PPI 正确 |

### 3.4 PMU 验证

#### 3.4.1 电源域控制测试

| 测试点 ID | 测试描述 | 优先级 | 测试类型 | 预期结果 |
|-----------|----------|--------|----------|----------|
| PMU-PD-001 | 电源域上电 | P0 | 功能 | 上电正确 |
| PMU-PD-002 | 电源域下电 | P0 | 功能 | 下电正确 |
| PMU-PD-003 | 上电序列 | P0 | 功能 | 序列正确 |
| PMU-PD-004 | 下电序列 | P0 | 功能 | 序列正确 |
| PMU-PD-005 | 电源域隔离 | P0 | 功能 | 隔离正确 |

#### 3.4.2 监控功能测试

| 测试点 ID | 测试描述 | 优先级 | 测试类型 | 预期结果 |
|-----------|----------|--------|----------|----------|
| PMU-MON-001 | 电压监控精度 | P0 | 功能 | 精度 ±1-2% |
| PMU-MON-002 | 温度监控精度 | P0 | 功能 | 精度 ±1°C |
| PMU-MON-003 | 电流监控精度 | P0 | 功能 | 精度 ±2-3% |
| PMU-MON-004 | 采样率测试 | P0 | 性能 | 1MHz 采样 |

#### 3.4.3 DVFS 测试

| 测试点 ID | 测试描述 | 优先级 | 测试类型 | 预期结果 |
|-----------|----------|--------|----------|----------|
| PMU-DVFS-001 | CPU DVFS | P0 | 功能 | 频率/电压正确 |
| PMU-DVFS-002 | NPU DVFS | P0 | 功能 | 频率/电压正确 |
| PMU-DVFS-003 | GPU DVFS | P0 | 功能 | 频率/电压正确 |
| PMU-DVFS-004 | 档位切换 | P0 | 功能 | 切换正确 |

#### 3.4.4 低功耗模式测试

| 测试点 ID | 测试描述 | 优先级 | 测试类型 | 预期结果 |
|-----------|----------|--------|----------|----------|
| PMU-LP-001 | Active 模式 | P0 | 功能 | 正常工作 |
| PMU-LP-002 | Idle 模式 | P0 | 功能 | 进入/退出 |
| PMU-LP-003 | Standby 模式 | P0 | 功能 | 进入/退出 |
| PMU-LP-004 | Sleep 模式 | P0 | 功能 | 进入/退出 |
| PMU-LP-005 | Deep Sleep 模式 | P0 | 功能 | 进入/退出 |
| PMU-LP-006 | Shutdown 模式 | P0 | 功能 | 进入/退出 |
| PMU-LP-007 | 唤醒源测试 | P0 | 功能 | 唤醒正确 |

#### 3.4.5 保护功能测试

| 测试点 ID | 测试描述 | 优先级 | 测试类型 | 预期结果 |
|-----------|----------|--------|----------|----------|
| PMU-PROT-001 | 过压保护 | P0 | 异常 | 检测并关断 |
| PMU-PROT-002 | 欠压保护 | P0 | 异常 | 检测并复位 |
| PMU-PROT-003 | 过流保护 | P0 | 异常 | 检测并响应 |
| PMU-PROT-004 | 过温保护 | P0 | 异常 | 检测并降频 |
| PMU-PROT-005 | 看门狗超时 | P0 | 异常 | 超时复位 |

### 3.5 Memory 子系统验证

#### 3.5.1 LPDDR5 控制器测试

| 测试点 ID | 测试描述 | 优先级 | 测试类型 | 预期结果 |
|-----------|----------|--------|----------|----------|
| MEM-LPDDR5-001 | 读操作 | P0 | 功能 | 读数据正确 |
| MEM-LPDDR5-002 | 写操作 | P0 | 功能 | 写数据正确 |
| MEM-LPDDR5-003 | 刷新操作 | P0 | 功能 | 刷新正确 |
| MEM-LPDDR5-004 | 初始化序列 | P0 | 功能 | 初始化正确 |
| MEM-LPDDR5-005 | 命令队列 | P0 | 功能 | 队列正确 |

#### 3.5.2 性能测试

| 测试点 ID | 测试描述 | 优先级 | 测试类型 | 预期结果 |
|-----------|----------|--------|----------|----------|
| MEM-PERF-001 | 带宽测试 | P0 | 性能 | 达到目标带宽 |
| MEM-PERF-002 | 延迟测试 | P0 | 性能 | 延迟符合规格 |
| MEM-PERF-003 | 并发访问 | P1 | 功能 | 并发正确 |

### 3.6 NoC 验证

#### 3.6.1 路由功能测试

| 测试点 ID | 测试描述 | 优先级 | 测试类型 | 预期结果 |
|-----------|----------|--------|----------|----------|
| NOC-ROUTE-001 | 目的地路由 | P0 | 功能 | 路由正确 |
| NOC-ROUTE-002 | 源路由 | P0 | 功能 | 路由正确 |
| NOC-ROUTE-003 | 广播路由 | P1 | 功能 | 广播正确 |
| NOC-ROUTE-004 | 组播路由 | P2 | 功能 | 组播正确 |

#### 3.6.2 QoS 测试

| 测试点 ID | 测试描述 | 优先级 | 测试类型 | 预期结果 |
|-----------|----------|--------|----------|----------|
| NOC-QOS-001 | 优先级仲裁 | P0 | 功能 | 仲裁正确 |
| NOC-QOS-002 | 流量整形 | P0 | 功能 | 整形正确 |
| NOC-QOS-003 | 带宽分配 | P0 | 功能 | 分配正确 |
| NOC-QOS-004 | 拥塞控制 | P0 | 功能 | 控制正确 |

### 3.7 外设接口验证

#### 3.7.1 PCIe 测试

| 测试点 ID | 测试描述 | 优先级 | 测试类型 | 预期结果 |
|-----------|----------|--------|----------|----------|
| PCIE-001 | 链路训练 | P0 | 功能 | 训练成功 |
| PCIE-002 | 事务层收发 | P0 | 功能 | 收发正确 |
| PCIE-003 | 配置空间访问 | P0 | 功能 | 访问正确 |
| PCIE-004 | 中断生成 | P0 | 功能 | 中断正确 |

#### 3.7.2 Ethernet 测试

| 测试点 ID | 测试描述 | 优先级 | 测试类型 | 预期结果 |
|-----------|----------|--------|----------|----------|
| ETH-001 | MAC 帧收发 | P0 | 功能 | 收发正确 |
| ETH-002 | PHY 接口 | P0 | 功能 | 接口正确 |
| ETH-003 | DMA 操作 | P0 | 功能 | DMA 正确 |
| ETH-004 | 流量控制 | P1 | 功能 | 控制正确 |

#### 3.7.3 USB 测试

| 测试点 ID | 测试描述 | 优先级 | 测试类型 | 预期结果 |
|-----------|----------|--------|----------|----------|
| USB-001 | 设备枚举 | P0 | 功能 | 枚举成功 |
| USB-002 | 数据传输 | P0 | 功能 | 传输正确 |
| USB-003 | 中断处理 | P0 | 功能 | 中断正确 |
| USB-004 | 电源管理 | P1 | 功能 | 管理正确 |

---

## 4. 验证环境架构

### 4.1 UVM 验证环境结构

```
05_Verification_DV/
├── uvm_env/                          # UVM 验证环境根目录
│   ├── common/                        # 公共组件
│   │   ├── vip/                       # 验证 IP 库
│   │   │   ├── axi4_vip/              # AXI4 VIP
│   │   │   ├── apb4_vip/              # APB4 VIP
│   │   │   ├── ahb_vip/               # AHB VIP
│   │   │   ├── uart_vip/              # UART VIP
│   │   │   ├── i2c_vip/               # I2C VIP
│   │   │   ├── spi_vip/               # SPI VIP
│   │   │   ├── gpio_vip/              # GPIO VIP
│   │   │   ├── pcie_vip/              # PCIe VIP
│   │   │   ├── ethernet_vip/          # Ethernet VIP
│   │   │   ├── usb_vip/               # USB VIP
│   │   │   └── jtag_vip/              # JTAG VIP
│   │   ├── scoreboard/                # Scoreboard 库
│   │   ├── coverage/                  # 覆盖率组件
│   │   └── sequence/                  # 序列库
│   │
│   ├── tb/                            # Testbench 顶层
│   │   ├── top_tb.sv                  # Testbench 顶层文件
│   │   ├── top_env.sv                 # 环境配置
│   │   └── tb_pkg.sv                  # 包定义
│   │
│   ├── agent/                         # 通用 Agent
│   │   ├── axi4_agent/                # AXI4 Agent
│   │   ├── apb4_agent/                # APB4 Agent
│   │   └── reset_agent/               # Reset Agent
│   │
│   ├── scoreboard/                    # Scoreboard 实现
│   │   ├── axi4_sb.sv                 # AXI4 Scoreboard
│   │   └── mem_sb.sv                  # 存储 Scoreboard
│   │
│   ├── coverage/                      # 覆盖率定义
│   │   ├── axi4_cov.sv                # AXI4 覆盖率
│   │   ├── func_cov.sv                # 功能覆盖率
│   │   └── assert_cov.sv              # 断言覆盖率
│   │
│   └── scripts/                       # 验证脚本
│       ├── run_sim.py                 # 仿真运行脚本
│       ├── run_regression.py          # 回归测试脚本
│       ├── gen_cov_report.py          # 覆盖率报告生成
│       └── check_coverage.py          # 覆盖率检查
│
├── testplan_block/                    # 模块测试计划
│   ├── safety_island/                 # Safety Island 测试计划
│   │   └── testplan_safety_island.md
│   ├── npu_cluster/                   # NPU Cluster 测试计划
│   │   └── testplan_npu_cluster.md
│   ├── cpu_subsystem/                 # CPU 子系统测试计划
│   │   └── testplan_cpu.md
│   ├── pmu/                           # PMU 测试计划
│   │   ├── testplan_pmu.md
│   │   └── FEATURE_LIST.md
│   ├── memory_ctrl/                   # 存储控制测试计划
│   │   └── testplan_mem_ctrl.md
│   ├── noc/                           # NoC 测试计划
│   │   └── testplan_noc.md
│   ├── pcie/                          # PCIe 测试计划
│   │   └── testplan_pcie.md
│   ├── ethernet/                      # Ethernet 测试计划
│   │   └── testplan_ethernet.md
│   ├── usb/                           # USB 测试计划
│   │   └── testplan_usb.md
│   ├── display/                       # Display 测试计划
│   │   └── testplan_display.md
│   ├── isp/                           # ISP 测试计划
│   │   └── testplan_isp.md
│   ├── gpu/                           # GPU 测试计划
│   │   └── testplan_gpu.md
│   ├── crypto/                        # Crypto 测试计划
│   │   └── testplan_crypto.md
│   ├── can/                           # CAN 测试计划
│   │   └── testplan_can.md
│   ├── i2c_spi_gpio/                  # I2C/SPI/GPIO 测试计划
│   │   └── testplan_i2c_spi_gpio.md
│   ├── audio/                         # Audio 测试计划
│   │   └── testplan_audio.md
│   └── debug/                         # Debug 测试计划
│       └── testplan_debug.md
│
├── testbench/                         # 模块级 Testbench
│   ├── safety_island_tb/              # Safety Island Testbench
│   ├── npu_cluster_tb/                # NPU Cluster Testbench
│   ├── cpu_subsystem_tb/              # CPU 子系统 Testbench
│   ├── pmu_tb/                        # PMU Testbench
│   ├── mem_ctrl_tb/                   # 存储控制 Testbench
│   ├── noc_tb/                        # NoC Testbench
│   └── ...
│
├── tests/                             # 测试用例
│   ├── safety_island_tests/           # Safety Island 测试
│   ├── npu_cluster_tests/             # NPU Cluster 测试
│   ├── cpu_subsystem_tests/           # CPU 子系统测试
│   ├── pmu_tests/                     # PMU 测试
│   └── ...
│
├── coverage_reports/                  # 覆盖率报告
│   ├── safety_island/                 # Safety Island 覆盖率
│   ├── npu_cluster/                   # NPU Cluster 覆盖率
│   └── ...
│
├── regression/                        # 回归测试
│   ├── regression_list.yaml           # 回归测试列表
│   ├── regression_config.yaml         # 回归测试配置
│   └── nightly_regression.sh          # 夜间回归脚本
│
└── docs/                              # 验证文档
    ├── dv_plan.md                     # 验证计划 (本文档)
    ├── verification_strategy.md       # 验证策略
    ├── coverage_model.md              # 覆盖率模型
    └── vip_spec.md                    # VIP 规格说明
```

### 4.2 UVM 组件结构

```
uvm_env/
├── src/
│   ├── pkg/                           # SystemVerilog 包
│   │   ├── uvm_pkg.sv                 # UVM 包引用
│   │   ├── dv_pkg.sv                  # DV 包定义
│   │   └── reg_pkg.sv                 # 寄存器包
│   │
│   ├── component/                     # UVM 组件
│   │   ├── env/                       # Environment
│   │   │   ├── base_env.sv            # 基础环境
│   │   │   ├── sim_env.sv             # 仿真环境
│   │   │   └── scoreboard.sv          # Scoreboard
│   │   │
│   │   ├── agent/                     # Agent
│   │   │   ├── axi4_agent.sv          # AXI4 Agent
│   │   │   ├── apb4_agent.sv          # APB4 Agent
│   │   │   ├── gpio_agent.sv          # GPIO Agent
│   │   │   └── irq_agent.sv           # 中断 Agent
│   │   │
│   │   ├── driver/                    # Driver
│   │   │   ├── axi4_driver.sv         # AXI4 Driver
│   │   │   └── apb4_driver.sv         # APB4 Driver
│   │   │
│   │   ├── monitor/                   # Monitor
│   │   │   ├── axi4_monitor.sv        # AXI4 Monitor
│   │   │   └── apb4_monitor.sv        # APB4 Monitor
│   │   │
│   │   ├── sequencer/                 # Sequencer
│   │   │   ├── axi4_sequencer.sv      # AXI4 Sequencer
│   │   │   └── apb4_sequencer.sv      # APB4 Sequencer
│   │   │
│   │   └── scoreboard/                # Scoreboard
│   │       ├── axi4_sb.sv             # AXI4 Scoreboard
│   │       └── mem_sb.sv              # 存储 Scoreboard
│   │
│   └── sequence/                      # Sequence
│       ├── base_sequence.sv           # 基础序列
│       ├── axi4_sequence.sv           # AXI4 序列
│       └── apb4_sequence.sv           # APB4 序列
│
└── vip/                               # Verification IP
    ├── axi4_vip/                      # AXI4 VIP
    │   ├── axi4_agent.sv
    │   ├── axi4_driver.sv
    │   ├── axi4_monitor.sv
    │   ├── axi4_sequencer.sv
    │   ├── axi4_sequence.sv
    │   ├── axi4_config.sv
    │   ├── axi4_coverage.sv
    │   └── axi4_assertions.sv
    │
    ├── apb4_vip/                      # APB4 VIP
    │   ├── apb4_agent.sv
    │   ├── apb4_driver.sv
    │   ├── apb4_monitor.sv
    │   ├── apb4_sequencer.sv
    │   ├── apb4_sequence.sv
    │   ├── apb4_config.sv
    │   ├── apb4_coverage.sv
    │   └── apb4_assertions.sv
    │
    ├── pcie_vip/                      # PCIe VIP
    │   ├── pcie_agent.sv
    │   ├── pcie_driver.sv
    │   ├── pcie_monitor.sv
    │   ├── pcie_sequencer.sv
    │   ├── pcie_sequence.sv
    │   └── pcie_config.sv
    │
    └── uart_vip/                      # UART VIP
        ├── uart_agent.sv
        ├── uart_driver.sv
        ├── uart_monitor.sv
        ├── uart_sequencer.sv
        ├── uart_sequence.sv
        └── uart_config.sv
```

---

## 5. 覆盖率模型

### 5.1 代码覆盖率目标

| 覆盖率类型 | 目标 | 说明 |
|------------|------|------|
| 行覆盖率 (Line) | ≥ 95% | 所有 RTL 代码 |
| 分支覆盖率 (Branch) | ≥ 95% | 所有条件分支 |
| 条件覆盖率 (Condition) | ≥ 90% | 所有复杂条件 |
| 翻转覆盖率 (Toggle) | ≥ 90% | 所有信号翻转 |
| 状态机覆盖率 (FSM) | 100% | 所有状态和跳转 |
| 断言覆盖率 (Assert) | ≥ 90% | 所有断言 |

### 5.2 功能覆盖率定义

| 模块 | 功能覆盖率点 | 目标 |
|------|-------------|------|
| Safety Island | 错误注入覆盖率 | 100% |
| NPU | 操作类型覆盖率 | 100% |
| PMU | 电源状态覆盖率 | 100% |
| NoC | 路由场景覆盖率 | 100% |

---

## 6. 回归测试策略

### 6.1 回归测试级别

| 级别 | 运行频率 | 测试用例数 | 执行时间 |
|------|----------|------------|----------|
| Sanity | 每次提交 | 50 | < 5分钟 |
| Nightly | 每日 | 500 | < 2小时 |
| Weekly | 每周 | 2000 | < 8小时 |
| Full | 发布前 | 5000 | < 24小时 |

### 6.2 缺陷管理

- **缺陷严重级别**:
  - Blocker: 阻塞验证
  - Critical: 功能严重错误
  - Major: 功能错误
  - Minor: 小问题
  - Trivial: 建议改进

---

## 7. 工具链配置

### 7.1 EDA 工具

| 工具 | 版本 | 用途 |
|------|------|------|
| VCS / Xcelium | 2023+ | RTL 仿真 |
| Questa | 2023+ | 仿真调试 |
| Verdi | 2023+ | 波形查看 |
| Verdi UVMC | 2023+ | 覆盖率分析 |

### 7.2 脚本环境

- **Python**: 3.8+
- **PyYAML**: 配置解析
- **ReportLab**: 报告生成
- **Jinja2**: 模板生成

---

## 8. 交付物清单

| 交付物 | 说明 | 状态 |
|--------|------|------|
| 验证计划 | 本文档 | 已交付 |
| 测试点分解 | 各模块测试点 | 进行中 |
| UVM 验证环境 | 完整 UVM 环境 | 进行中 |
| VIP 库 | 验证 IP | 进行中 |
| 测试用例 | 所有测试用例 | 进行中 |
| 覆盖率报告 | 各模块覆盖率 | 待交付 |
| 验证报告 | 最终验证报告 | 待交付 |

---

## 9. 风险与应对

| 风险 | 影响 | 概率 | 应对措施 |
|------|------|------|----------|
| 覆盖率不达标 | 验证延期 | 中 | 增加测试用例，优化约束 |
| RTL Bug 过多 | 验证周期延长 | 中 | 提前进行设计评审 |
| 仿真速度慢 | 回归时间过长 | 高 | 使用硬件加速 |
| VIP 质量问题 | 验证准确性 | 低 | 充分 VIP 验证 |

---

**文档版本**: V1.0
**创建日期**: 2026-01-18
**最后更新**: 2026-01-18
**负责人**: DV 验证工程师

---

**审批**:

| 角色 | 姓名 | 签名 | 日期 |
|------|------|------|------|
| DV 验证工程师 | - | - | - |
| 设计工程师 | - | - | - |
| 架构师 | - | - | - |
