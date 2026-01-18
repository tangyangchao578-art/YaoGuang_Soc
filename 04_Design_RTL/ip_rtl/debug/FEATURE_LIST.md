# Debug Module Feature List

## Overview
This document lists all features and capabilities of the YaoGuang SoC Debug Module.

## Version Information
- **Version**: 1.0
- **Date**: 2026-01-18
- **Status**: Draft

---

## 1. Debug Interfaces

### 1.1 JTAG Interface
| Feature | Status | Description |
|---------|--------|-------------|
| IEEE 1149.1 Compliant | ✅ | Full JTAG boundary-scan support |
| TCK Frequency | ✅ | Up to 20 MHz |
| TAP Controller | ✅ | 16-state standard FSM |
| Instruction Register | ✅ | 5-bit IR (configurable) |
| Supported Instructions | ✅ | BYPASS, IDCODE, SAMPLE, EXTEST, DEBUG, HIGHZ |
| IDCODE Read | ✅ | 32-bit chip identification |

### 1.2 SWD Interface
| Feature | Status | Description |
|---------|--------|-------------|
| ARM Debug Interface v5 | ✅ | Full SWD protocol support |
| SWCLK Frequency | ✅ | Up to 100 MHz |
| Bidirectional I/O | ✅ | Open-drain SWDIO |
| Protocol Handling | ✅ | ACK/WAIT/FAULT responses |
| Retry Logic | ✅ | Automatic retry on WAIT |

### 1.3 Trace Port Interface
| Feature | Status | Description |
|---------|--------|-------------|
| TPIU Implementation | ✅ | Full CoreSight TPIU |
| Data Width | ✅ | 8/16/32-bit configurable |
| Maximum Bandwidth | ✅ | 8 Gbps (32-bit DDR @ 125MHz) |
| Sync Packets | ✅ | Frame synchronization |
| Continuous Mode | ✅ | Non-stop data output |

---

## 2. CoreSight Components

### 2.1 Debug Access Port (DAP)
| Feature | Status | Description |
|---------|--------|-------------|
| APB-AP | ✅ | APB access port |
| AHB-AP | ✅ | AHB access port (optional) |
| ROM Table | ✅ | 1KB debug ROM |
| ID Code | ✅ | 0xBA00477 (YaoGuang) |
| Transaction Queue | ✅ | 4-deep outstanding |

### 2.2 CPU Debug Components
| Feature | Status | Description |
|---------|--------|-------------|
| Hardware Breakpoints | ✅ | 4 per CPU core |
| Software Breakpoints | ✅ | Unlimited (BKPT instruction) |
| Watchpoints | ✅ | 4 per CPU core |
| Breakpoint Types | ✅ | Execute, Access, Conditional |
| Debug State Machine | ✅ | Halting/Monitor modes |

### 2.3 Trace Macrocells
| Feature | Status | Description |
|---------|--------|-------------|
| ETM per CPU | ✅ | 4 CPU ETMs |
| ITM | ✅ | 8 software channels |
| STM | ✅ | System trace (optional) |
| Branch History | ✅ | Compressed trace mode |
| Cycle Accurate | ✅ | Timing精确跟踪 |

---

## 3. Trace Capabilities

### 3.1 Trace Aggregation
| Feature | Status | Description |
|---------|--------|-------------|
| Multi-Source | ✅ | Up to 6 trace sources |
| Round-Robin Arbitration | ✅ | Fair bandwidth sharing |
| Priority Queuing | ✅ | Configurable priority |
| ATB Compliant | ✅ | ARM Trace Bus protocol |

### 3.2 Trace Buffer
| Feature | Status | Description |
|---------|--------|-------------|
| Buffer Size | ✅ | 8 MB SRAM |
| Circular Mode | ✅ | Overwrite oldest data |
| Trigger Support | ✅ | Hardware trigger |
| Watermark Interrupt | ✅ | Configurable threshold |
| Read Interface | ✅ | AHB/APB accessible |

---

## 4. Debug Functions

### 4.1 Execution Control
| Feature | Status | Description |
|---------|--------|-------------|
| CPU Halt/Resume | ✅ | All cores simultaneously |
| Single Step | ✅ | Per-instruction stepping |
| Monitor Mode | ✅ | Software debug handler |
| Multi-Master | ✅ | Multiple debuggers |

### 4.2 Memory Access
| Feature | Status | Description |
|---------|--------|-------------|
| Memory Read/Write | ✅ | Through DAP |
| Memory Compare | ✅ | Read-modify-write |
| Block Transfer | ✅ | DMA-assisted transfers |
| ECC Support | ✅ | Memory error detection |

### 4.3 Register Access
| Feature | Status | Description |
|---------|--------|-------------|
| GPR Access | ✅ | General purpose registers |
| SPR Access | ✅ | Special purpose registers |
| CSR Access | ✅ | Control and status registers |
| Vector Registers | ✅ | SIMD/Vector registers |

---

## 5. Performance Analysis

### 5.1 Performance Counters
| Feature | Status | Description |
|---------|--------|-------------|
| Core Counters | ✅ | 8 per CPU (32 total) |
| Cache Metrics | ✅ | Hit/Miss/Evict counts |
| Branch Metrics | ✅ | Predict/Taken/ Miss counts |
| Memory Latency | ✅ | Access latency histogram |
| Custom Events | ✅ | User-defined counters |

### 5.2 Bandwidth Monitoring
| Feature | Status | Description |
|---------|--------|-------------|
| Bus Utilization | ✅ | Per-master tracking |
| Peak Bandwidth | ✅ | Real-time monitoring |
| Average Bandwidth | ✅ | Windowed statistics |
| Hotspot Detection | ✅ | Address range analysis |

---

## 6. Security Features

### 6.1 Access Control
| Feature | Status | Description |
|---------|--------|-------------|
| Debug Enable | ✅ | OTP-controlled |
| Secure Debug | ✅ | Authenticated access |
| Domain Isolation | ✅ | Security domain checks |
| JTAG Disable | ✅ | Fuse-based disable |

### 6.2 Data Protection
| Feature | Status | Description |
|---------|--------|-------------|
| Trace Encryption | ✅ | AES-128 (optional) |
| HMAC Integrity | ✅ | SHA-256 (optional) |
| Secure Key Storage | ✅ | eFuse/OTP |

---

## 7. Safety Features (ISO 26262)

### 7.1 Safety Mechanisms
| Feature | Status | Description |
|---------|--------|-------------|
| Lockstep Verification | ✅ | Redundant compare |
| Error Detection | ✅ | Parity/ECC on registers |
| Timeout Protection | ✅ | Watchdog timers |
| Fault Injection Test | ✅ | Test modes |

### 7.2 Diagnostic Coverage
| Feature | Status | Description |
|---------|--------|-------------|
| Single Point Fault | ✅ | Coverage metrics |
| Latent Fault | ✅ | Detection coverage |
| Dependent Failure | ✅ | Common cause analysis |

---

## 8. Implementation Metrics

### 8.1 Area
| Component | Area (mm²) | Gate Count (K) |
|-----------|------------|----------------|
| DAP | 0.05 | 12 |
| JTAG | 0.02 | 5 |
| SWD | 0.01 | 3 |
| TPIU | 0.03 | 8 |
| ETM (x4) | 0.40 | 100 |
| ITM | 0.02 | 5 |
| Trace Buffer | 0.50 | 125 |
| Matrix | 0.08 | 20 |
| **Total** | **~1.1** | **~278** |

### 8.2 Power
| Mode | Dynamic (mW) | Static (mW) |
|------|--------------|-------------|
| Idle | 5 | 1 |
| Active Trace | 22 | 2 |
| Peak | 35 | 3 |

---

## 9. Verification Status

### 9.1 Simulation
| Test Category | Status | Coverage |
|---------------|--------|----------|
| JTAG Protocol | ✅ Pass | 100% |
| SWD Protocol | ✅ Pass | 100% |
| DAP Access | ✅ Pass | 100% |
| Trace Routing | ✅ Pass | 95% |
| Buffer Operations | ✅ Pass | 100% |

### 9.2 Formal Verification
| Property | Status |
|----------|--------|
| TAP FSM | ✅ Verified |
| Arbitration | ✅ Verified |
| Buffer Overflow | ✅ Verified |

---

## 10. Compliance

| Standard | Compliance Level |
|----------|-----------------|
| IEEE 1149.1 | Full |
| ARM CoreSight | Full |
| ARM Debug Interface v5 | Full |
| ISO 26262 ASIL-D | Target |

---

## Document Revision

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2026-01-18 | YaoGuang Arch | Initial release |
