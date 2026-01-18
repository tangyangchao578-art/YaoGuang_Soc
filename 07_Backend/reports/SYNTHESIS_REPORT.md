# YaoGuang SoC Synthesis Report

## Executive Summary

**Design**: YaoGuang Automotive SoC  
**Process**: TSMC 5nm  
**Target Frequency**: 2.0 GHz (Core/NPU), 500 MHz (System)  
**Synthesis Status**: Ready to Run  
**Report Version**: V1.0  
**Date**: 2026-01-18

---

## 1. Synthesis Configuration

### 1.1 Tool Configuration

| Parameter | Value |
|-----------|-------|
| Synthesis Tool | Synopsys Design Compiler |
| Target Library | SAED5nm (typical) |
| Optimization Goal | Balanced (Timing/Area/Power) |
| Compile Strategy | compile_ultra |
| Clock Gating | Integrated clock gating cells |
| Wire Load Model | Automatic selection |

### 1.2 Library Information

```
Target Library: saed5nm_typ.db
Min Library:    saed5nm_min.db
Max Library:    saed5nm_max.db
Symbol Library: saed5nm.sdb
```

---

## 2. Design Statistics

### 2.1 RTL File Count

| Category | File Count |
|----------|------------|
| Top-level | 2 |
| Subsystems | 6 |
| IP Modules | 22 |
| **Total** | **30** |

### 2.2 RTL Module Hierarchy

```
yaoguang_soc (top)
├── cpu_subsystem
│   ├── cpu_cluster (4× Cortex-A78AE)
│   └── interrupt_controller
├── npu_subsystem
│   └── npu_cluster (4× NPU)
├── gpu_subsystem
│   └── gpu_core (Mali-G78)
├── isp_subsystem
│   └── isp_pipeline
├── memory_subsystem
│   ├── ddr_controller
│   └── l3_cache
└── io_subsystem
    ├── pcie_controller
    ├── gmac_controller
    ├── usb_controller
    ├── spi_controller
    ├── i2c_controller
    ├── uart_controller
    └── gpio_controller
```

---

## 3. Clock Domain Summary

### 3.1 Primary Clocks

| Clock Name | Frequency | Period | Source | Uncertainty |
|------------|-----------|--------|--------|-------------|
| clk_core | 2.0 GHz | 0.5 ns | clk_core | 50 ps |
| clk_npu | 2.0 GHz | 0.5 ns | clk_npu | 50 ps |
| clk_gpu | 1.0 GHz | 1.0 ns | clk_gpu | 40 ps |
| clk_sys | 500 MHz | 2.0 ns | clk_sys | 30 ps |
| clk_mem | 800 MHz | 1.25 ns | clk_mem | 40 ps |
| clk_isp | 600 MHz | 1.67 ns | clk_isp | 35 ps |
| clk_display | 300 MHz | 3.33 ns | clk_display | 30 ps |
| clk_pcie | 250 MHz | 4.0 ns | clk_pcie_ref | 50 ps |
| clk_eth | 250 MHz | 4.0 ns | clk_eth_ref | 50 ps |
| clk_usb | 250 MHz | 4.0 ns | clk_usb_ref | 50 ps |
| clk_audio | 100 MHz | 10.0 ns | clk_audio | 25 ps |
| clk_apb | 100 MHz | 10.0 ns | clk_apb | 25 ps |
| clk_rtc | 32.768 kHz | 30.5 μs | clk_rtc | 500 ps |

### 3.2 Clock Relationships

| Group | Type | Clocks |
|-------|------|--------|
| clk_core_group | Synchronous | clk_core, clk_core_div2, clk_core_div4 |
| clk_npu_group | Synchronous | clk_npu, clk_npu_div2, clk_npu_div4 |
| clk_gpu_group | Synchronous | clk_gpu, clk_gpu_div2 |
| core_npu_sync | Asynchronous | clk_core ↔ clk_npu |
| async_sys_periph | Asynchronous | clk_sys, clk_pcie, clk_eth, clk_usb |
| async_slow_clocks | Asynchronous | clk_audio, clk_apb, clk_rtc |

---

## 4. IO Constraints Summary

### 4.1 High-Speed IO

| Interface | Data Rate | Clock | Input Delay | Output Delay |
|-----------|-----------|-------|-------------|--------------|
| DDR5/LPDDR5 | 6400 MT/s | ddr_dqs* | 0.1-0.3 ns | -0.1 to 0.3 ns |
| PCIe Gen4 | 16 GT/s | clk_pcie | 0-0.1 ns | -0.1 to 0.1 ns |
| 10G Ethernet | 10.3125 Gbps | eth_rx_clk | 0.1-0.3 ns | -0.1 to 0.3 ns |
| USB 3.2 | 10 GT/s | usb_ref_clk | 0.05-0.2 ns | -0.1 to 0.2 ns |

### 4.2 General Purpose IO

| Interface | Clock | Max Input Delay | Max Output Delay |
|-----------|-------|-----------------|------------------|
| System | clk_sys | 0.8 ns | 0.8 ns |
| APB Peripherals | clk_apb | 1.5 ns | 1.5 ns |

---

## 5. Expected Synthesis Results

### 5.1 Estimated Gate Count

| Module | Estimated Gates | Notes |
|--------|-----------------|-------|
| Cortex-A78AE (×4) | 8,000,000 | Per core |
| Cortex-R52 (×2) | 500,000 | Per core |
| NPU Cluster (×4) | 15,000,000 | Per cluster |
| Mali-G78 | 5,000,000 | GPU core |
| ISP Pipeline | 2,000,000 | Image signal processor |
| NoC Router | 3,000,000 | 16-port mesh |
| DDR Controller | 1,500,000 | DDR5/LPDDR5 |
| PCIe Controller | 800,000 | Gen4 ×8 + ×4 |
| Ethernet MAC | 500,000 | 10G |
| USB Controller | 400,000 | 3.2 |
| Security Engine | 1,000,000 | Crypto/PUF |
| Other Peripherals | 2,000,000 | GPIO/I2C/SPI/UART |
| **Total** | **~50,000,000** | |

### 5.2 Estimated Area

| Category | Area (mm²) | Percentage |
|----------|------------|------------|
| CPU Cluster | 8.0 | 16% |
| NPU Cluster | 40.0 | 80% |
| GPU | 5.0 | 10% |
| NoC/Interconnect | 2.0 | 4% |
| Memory (L3 Cache) | 3.0 | 6% |
| Peripherals | 1.5 | 3% |
| **Total** | **~50.0** | **100%** |

*Note: Area estimates based on TSMC 5nm standard cell library. Actual area will be refined after synthesis.*

### 5.3 Estimated Power

| Component | Dynamic Power (W) | Leakage Power (W) | Total (W) |
|-----------|-------------------|-------------------|-----------|
| CPU (4× A78AE) | 8.0 | 0.5 | 8.5 |
| Safety Island (2× R52) | 0.5 | 0.05 | 0.55 |
| NPU (4× Cluster) | 15.0 | 1.0 | 16.0 |
| GPU (Mali-G78) | 2.0 | 0.2 | 2.2 |
| NoC | 1.0 | 0.1 | 1.1 |
| Memory | 0.8 | 0.05 | 0.85 |
| Peripherals | 0.5 | 0.05 | 0.55 |
| **Total** | **27.8** | **1.95** | **29.75** |

*Target Power Budget: < 30W ✓*

---

## 6. Multi-Cycle Path Constraints

| Path | Setup Multi-Cycle | Hold Multi-Cycle |
|------|-------------------|------------------|
| DDR ↔ Core | 2 | 1 |
| Async FIFO (Core→Sys) | 2 | 1 |
| Async FIFO (NPU→Sys) | 2 | 1 |
| Mem Ctrl → CPU | 3 | 2 |
| ISP → Display | 3 | 2 |

---

## 7. False Path Constraints

| Category | Rationale |
|----------|-----------|
| Scan Chain | Test logic, timing controlled by ATPG |
| JTAG | Debug interface, low speed |
| ARM DAP | Debug access port |
| Memory BIST | Built-in self test |
| PLL Config | Static configuration |
| Clock Gating | Control signals |
| Reset Sync | Asynchronous reset domain crossing |
| Power Management | Power state control signals |
| Temperature Sensor | Slow sensor interface |
| RTC Domain | 32 kHz slow clock |

---

## 8. Synthesis Script Flow

### 8.1 Script Sequence

```
1. setup_dc.tcl        # Environment and library setup
2. dc_synthesis.tcl    # Main synthesis script
   ├── Step 1: Read RTL Files
   ├── Step 2: Apply Constraints (SDC)
   ├── Step 3: Constraint Checking
   ├── Step 4: Link Design
   ├── Step 5: Area Optimization (Pass 1)
   ├── Step 6: Timing Optimization (Pass 2)
   ├── Step 7: Clock Gating Optimization
   ├── Step 8: Power Optimization
   ├── Step 9: Final Optimization
   ├── Step 10: Generate Reports
   └── Step 11: Save Outputs
```

### 8.2 Output Files

| File | Description |
|------|-------------|
| `yaoguang_soc_netlist.v` | Synthesized gate-level netlist |
| `yaoguang_soc_sdc.out.sdc` | Output SDC with applied constraints |
| `yaoguang_soc.ddc` | Design database for further editing |
| `area.rpt` | Detailed area report |
| `area_summary.rpt` | Area summary |
| `timing.rpt` | Full timing report (50 worst paths) |
| `timing_critical.rpt` | Critical timing paths |
| `timing_clock_groups.rpt` | Clock group timing analysis |
| `power.rpt` | Power report |
| `power_detailed.rpt` | Detailed power analysis |
| `clock.rpt` | Clock network report |
| `clock_gating.rpt` | Clock gating report |
| `constraints_violators.rpt` | Constraint violations |
| `path_analysis.rpt` | Path analysis report |
| `check_design.rpt` | Design rule checks |
| `check_timing.rpt` | Timing constraint checks |
| `synthesis.log` | Execution log |

---

## 9. Timing Constraints Verification

### 9.1 Clock Definition Check

| Clock | Period | Source Latency | Network Latency | Total Latency |
|-------|--------|----------------|-----------------|---------------|
| clk_core | 0.5 ns | 50-150 ps | 20-80 ps | 70-230 ps |
| clk_npu | 0.5 ns | 50-150 ps | 20-80 ps | 70-230 ps |
| clk_sys | 2.0 ns | 80-200 ps | 20-60 ps | 100-260 ps |
| clk_mem | 1.25 ns | 50-120 ps | 20-80 ps | 70-200 ps |

### 9.2 IO Timing Check

| Interface | Data Rate | Required Setup | Required Hold |
|-----------|-----------|----------------|---------------|
| DDR5 | 6400 MT/s | 0.3 ns | 0.1 ns |
| PCIe | 16 GT/s | 0.1 ns | 0.05 ns |
| Ethernet | 10 Gbps | 0.3 ns | 0.1 ns |
| USB | 10 GT/s | 0.2 ns | 0.05 ns |

---

## 10. Next Steps After Synthesis

1. **DFT Insertion**: Run `dft/dft_insertion.tcl`
   - Insert scan chains (16 chains, 10x compression)
   - Target: Scan coverage > 95%

2. **Formal Verification**: Verify equivalence between RTL and gate-level netlist
   - Tool: Synopsys Formality
   - Check: RTL vs. Synthesized Netlist

3. **Physical Design**: Import netlist to ICC2
   - Floorplan creation
   - Macro placement
   - Power grid design

4. **Timing Analysis**: Run PrimeTime signoff
   - Setup analysis (WNS < 0)
   - Hold analysis (WNS < 0)
   - Signoff: Zero violations

---

## 11. Quality Metrics

### 11.1 Synthesis Quality Targets

| Metric | Target | Description |
|--------|--------|-------------|
| Timing | WNS > 0 | No setup violations |
| Area | < 60 mm² | Core utilization < 70% |
| Power | < 30 W | Total chip power |
| Clock Gating | > 95% | Gated register percentage |
| Leakage | < 2 W | Standby power |

### 11.2 DFT Quality Targets

| Metric | Target |
|--------|--------|
| Scan Coverage | > 95% |
| ATPG Compression | 10x |
| Test Coverage | > 99% |
| Fault Coverage | > 99% |

---

## 12. Known Issues and Mitigations

### 12.1 Potential Timing Challenges

| Issue | Mitigation |
|-------|------------|
| 2.0 GHz clock domain | Aggressive optimization, multiple PVT corners |
| Cross-domain paths | Synchronizers, multi-cycle paths |
| High fanout nets | Buffering, clock tree synthesis |
| IO timing (DDR5) | IO register placement, timing margins |

### 12.2 Area Optimization Strategies

| Strategy | Impact |
|----------|--------|
| Inferred memory mapping | ~5% area reduction |
| Constant propagation | ~2% area reduction |
|资源共享 | ~3% area reduction |
| Physical aware synthesis | ~5% area reduction |

---

## 13. Revision History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| V1.0 | 2026-01-18 | Backend Team | Initial release |

---

## 14. Approval

| Role | Name | Signature | Date |
|------|------|-----------|------|
| Backend Lead | ___________ | ___________ | ______ |
| Project Manager | ___________ | ___________ | ______ |
| Design Manager | ___________ | ___________ | ______ |

---

*End of Report*
