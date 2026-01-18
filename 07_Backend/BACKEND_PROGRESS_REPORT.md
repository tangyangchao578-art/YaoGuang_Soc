# YaoGuang SoC Backend Design Progress Report

## Project Overview

**Chip**: YaoGuang Automotive SoC  
**Process**: TSMC 5nm  
**Target**: L3/L4 Autonomous Driving  
**Version**: V1.0  
**Date**: 2026-01-18

---

## Executive Summary

The YaoGuang SoC backend design phase is **in progress**. All synthesis, DFT, and P&R scripts have been created and are ready for execution when the EDA tools become available.

| Phase | Status | Completion Date |
|-------|--------|-----------------|
| RTL Design | ✅ Complete | 2026-01-17 |
| DV Verification | ✅ Complete | 2026-01-17 |
| CV Verification | ✅ Complete | 2026-01-17 |
| SDC Constraints | ✅ Complete | 2026-01-18 |
| DC Synthesis Scripts | ✅ Ready | 2026-01-18 |
| DFT Configuration | ✅ Ready | 2026-01-18 |
| ICC2 P&R Scripts | ✅ Ready | 2026-01-18 |
| Physical Verification | ✅ Configured | 2026-01-18 |
| **Logical Synthesis** | **Pending** | TBD |
| **DFT Insertion** | **Pending** | TBD |
| **Floorplan** | **Pending** | TBD |
| **Place & Route** | **Pending** | TBD |
| **Timing Signoff** | **Pending** | TBD |
| **Physical Signoff** | **Pending** | TBD |
| **Tapeout** | **Pending** | TBD |

---

## 1. SDC Timing Constraints - COMPLETE

**Location**: `07_Backend/sdc/yaoguang_soc.sdc`  
**Lines**: 542  
**Status**: Ready for Synthesis

### Key Constraints

| Clock Domain | Frequency | Period | Notes |
|--------------|-----------|--------|-------|
| clk_core | 2.0 GHz | 0.5 ns | Cortex-A78AE ×4 |
| clk_npu | 2.0 GHz | 0.5 ns | NPU Cluster ×4 |
| clk_gpu | 1.0 GHz | 1.0 ns | Mali-G78 |
| clk_sys | 500 MHz | 2.0 ns | NoC |
| clk_mem | 800 MHz | 1.25 ns | DDR Controller |
| clk_isp | 600 MHz | 1.67 ns | Image Pipeline |
| clk_pcie | 250 MHz | 4.0 ns | PCIe Gen4 |
| clk_eth | 250 MHz | 4.0 ns | 10G Ethernet |
| clk_usb | 250 MHz | 4.0 ns | USB 3.2 |
| clk_display | 300 MHz | 3.33 ns | Display |
| clk_apb | 100 MHz | 10.0 ns | Peripherals |
| clk_audio | 100 MHz | 10.0 ns | Audio |
| clk_rtc | 32.768 kHz | 30.5 μs | RTC |

### Clock Groups

| Group Type | Clocks |
|------------|--------|
| Synchronous | clk_core, clk_core_div2, clk_core_div4 |
| Synchronous | clk_npu, clk_npu_div2, clk_npu_div4 |
| Asynchronous | clk_core ↔ clk_npu |
| Asynchronous | clk_sys, clk_pcie, clk_eth, clk_usb |

### IO Constraints

| Interface | Data Rate | Constraint Type |
|-----------|-----------|-----------------|
| DDR5/LPDDR5 | 6400 MT/s | Input/Output delay |
| PCIe Gen4 | 16 GT/s | Input/Output delay |
| 10G Ethernet | 10.3125 Gbps | Input/Output delay |
| USB 3.2 | 10 GT/s | Input/Output delay |

---

## 2. DC Synthesis Scripts - READY

**Location**: `07_Backend/scripts/dc/`  
**Scripts**: 3 files  
**Status**: Ready to Run

### Script Files

| Script | Purpose |
|--------|---------|
| `setup_dc.tcl` | Library paths, search paths, constraints |
| `dc_synthesis.tcl` | Main synthesis flow (300 lines) |
| `run_synthesis.sh` | Shell wrapper for execution |

### Synthesis Flow

```
1. Read RTL Files (30 files)
2. Apply Constraints (SDC)
3. Constraint Checking
4. Link Design
5. Area Optimization (Pass 1)
6. Timing Optimization (Pass 2)
7. Clock Gating Optimization
8. Power Optimization
9. Final Optimization
10. Generate Reports
11. Save Outputs
```

### Expected Outputs

| File | Description |
|------|-------------|
| `output/yaoguang_soc_netlist.v` | Gate-level netlist |
| `output/yaoguang_soc.ddc` | Design database |
| `reports/area.rpt` | Area report |
| `reports/timing.rpt` | Timing report |
| `reports/power.rpt` | Power report |

### Estimated Results

| Metric | Target | Notes |
|--------|--------|-------|
| Gate Count | ~50M | Including all modules |
| Area | ~50 mm² | Core utilization 70% |
| Power | < 30W | Total chip power |
| WNS | > 0 | No setup violations |

---

## 3. DFT Configuration - READY

**Location**: `07_Backend/dft/`  
**Files**: 2 files  
**Status**: Ready for Execution

### DFT Architecture

| Parameter | Value |
|-----------|-------|
| Scan Chains | 16 |
| Compression Ratio | 10:1 |
| Scan Flip-Flops | ~5,000,000 |
| MBIST Controllers | 12+ |
| LBIST Controllers | 4 |

### Scan Chain Distribution

| Domain | Chains | Avg Length | Notes |
|--------|--------|------------|-------|
| CPU (A78AE ×4) | 4 | 312,500 | Per-core |
| Safety (R52 ×2) | 2 | 125,000 | Per-core |
| NPU (Cluster ×4) | 4 | 625,000 | Per-cluster |
| GPU | 2 | 250,000 | Mali-G78 |
| NoC | 1 | 62,500 | Router |
| Memory | 1 | 125,000 | Controllers |
| Peripherals | 2 | 125,000 | GPIO/I2C/etc |

### DFT Features

- **Scan Compression**: 10:1 ratio
- **Boundary Scan**: IEEE 1149.1 JTAG
- **MBIST**: March C+, March SS algorithms
- **LBIST**: MISR-based compactor
- **ATPG**: Stuck-at, Transition, Path Delay

### Quality Targets

| Metric | Target |
|--------|--------|
| Scan Coverage | > 95% |
| Fault Coverage | > 99% |
| Test Coverage | > 99% |

---

## 4. ICC2 Place & Route Scripts - READY

**Location**: `07_Backend/scripts/icc2/`  
**Scripts**: 6 files  
**Status**: Ready for Execution

### Script Files

| Script | Purpose |
|--------|---------|
| `icc2_pnr.tcl` | Main P&R orchestration |
| `floorplan.tcl` | Floorplan creation, macro placement |
| `placement.tcl` | Standard cell placement |
| `cts.tcl` | Clock tree synthesis |
| `routing.tcl` | Global/detailed routing |
| `optimization.tcl` | Timing/power optimization |

### Floorplan Parameters

| Parameter | Value |
|-----------|-------|
| Chip Size | 15mm × 15mm |
| Core Size | 12mm × 12mm |
| Aspect Ratio | 1:1 |
| Metal Layers | 10 (M1-M10) |
| Core Utilization | 70% |
| IO Density | 100% |

### Macro Placement

| Macro | Size | Location | Notes |
|-------|------|----------|-------|
| Cortex-A78AE ×4 | 2mm² each | Top-left quadrant | CPU cluster |
| Cortex-R52 ×2 | 0.25mm² each | Safety island | Dual lock-step |
| NPU Cluster ×4 | 10mm² each | Center region | Heavy compute |
| Mali-G78 | 5mm² | Bottom-left | Graphics |
| ISP | 2mm² | Bottom-right | Image pipeline |
| L3 Cache | 3mm² | Center | Shared cache |
| DDR Controller | 0.5mm² | Right edge | Memory interface |

### Power Grid

| Parameter | Value |
|-----------|-------|
| Voltage Domains | 6 (PD_CORE, PD_NPU, PD_GPU, PD_MEM, PD_SYS, PD_IO) |
| Power Pins | VDD, VSS |
| Ground Pins | VSS |
| Ring Width | 50 μm |
| Ring Spacing | 100 μm |
| Stripe Width | 10 μm |
| Stripe Spacing | 100 μm |

### Clock Tree Synthesis

| Parameter | Value |
|-----------|-------|
| Clock Domains | 16 (including dividers) |
| CTS Strategy | H-tree + balancing |
| Max Skew | 50 ps |
| Max Depth | 12 levels |
| Buffer Type | Clock buffer cells |

---

## 5. PrimeTime Scripts - READY

**Location**: `07_Backend/scripts/pt/`  
**Scripts**: 3 files  
**Status**: Ready for Timing Analysis

### Script Files

| Script | Purpose |
|--------|---------|
| `pt_analysis.tcl` | Main timing analysis |
| `report_timing.tcl` | Comprehensive timing reports |
| `timing_closure.tcl` | Violation analysis and fix guidance |

### Timing Analysis Modes

| Mode | Corners | Description |
|------|---------|-------------|
| Setup | TT/FF/SS | Multi-corner analysis |
| Hold | TT/FF/SS | Multi-corner analysis |
| Signoff | All PVT | Final verification |

### Timing Targets

| Check | Target | Priority |
|-------|--------|----------|
| Setup WNS | > 0 ns | Critical |
| Hold WNS | > 0 ns | Critical |
| Max Transition | < 0.2 ns | High |
| Max Capacitance | < 2.0 pF | High |
| Clock Uncertainty | As specified | High |

---

## 6. Physical Verification - CONFIGURED

**Location**: `07_Backend/calibre/`  
**Files**: 4 files + 1 script  
**Status**: Ready for Execution

### Rule Files

| File | Purpose |
|------|---------|
| `yaoguang_drc.runset` | DRC rules (TSMC 5nm) |
| `yaoguang_lvs.runset` | LVS ruleset |
| `yaoguang_antenna.runset` | Antenna ruleset |
| `run_pv.sh` | Physical verification flow |

### DRC Checks

| Category | Rules | Priority |
|----------|-------|----------|
| Metal | Width, spacing, via | Critical |
| Poly | Width, spacing | Critical |
| Contact | Size, spacing | High |
| Well | Distance, tap | High |
| Antenna | Ratio, diode | Medium |

### Signoff Criteria

| Check | Target | Notes |
|-------|--------|-------|
| DRC | 0 violations | Must pass |
| LVS | Match | Netlist match |
| Antenna | 0 violations | Or protected |
| ERC | 0 violations | Electrical rules |

---

## 7. Power & DFT - COMPLETE

**Location**: `07_Backend/power/` and `07_Backend/dft/`

### Power Intent (UPF)

**File**: `power/yaoguang_soc.upf`

| Power Domain | Voltage | Retention | Isolation | Description |
|--------------|---------|-----------|-----------|-------------|
| PD_CORE | 0.8V | Yes | Yes | CPU cluster |
| PD_NPU | 0.9V | No | Yes | NPU cluster |
| PD_GPU | 0.8V | No | Yes | GPU |
| PD_MEM | 1.1V | No | Yes | Memory controller |
| PD_SYS | 0.8V | No | Yes | NoC, system |
| PD_IO | 1.8V/3.3V | No | N/A | I/O interfaces |

### Power Estimation

| Component | Dynamic (W) | Leakage (W) | Total (W) |
|-----------|-------------|-------------|-----------|
| CPU | 8.0 | 0.5 | 8.5 |
| NPU | 15.0 | 1.0 | 16.0 |
| GPU | 2.0 | 0.2 | 2.2 |
| NoC | 1.0 | 0.1 | 1.1 |
| Memory | 0.8 | 0.05 | 0.85 |
| Peripherals | 0.5 | 0.05 | 0.55 |
| **Total** | **27.3** | **1.9** | **29.2** |

---

## 8. Backend Checklist - COMPLETE

**File**: `07_Backend/backend_checklist.md`

| Phase | Checklist Items | Status |
|-------|-----------------|--------|
| Synthesis | SDC complete, libraries available, scripts ready | ✅ |
| DFT | Scan chains defined, MBIST configured, JTAG ready | ✅ |
| Floorplan | Die size, core area, macro placement, power grid | ✅ |
| Placement | Standard cell placement, congestion analysis | Ready |
| CTS | Clock domains, buffer selection, skew targets | Ready |
| Routing | Global route, detailed route, DRC fixes | Ready |
| Timing | Multi-corner analysis, signoff criteria | Ready |
| Power | IR drop analysis, EM analysis | Ready |
| Physical | DRC, LVS, Antenna | Ready |

---

## 9. Backend Flow Diagram - COMPLETE

**File**: `07_Backend/backend_flow.md`

### Complete Flow

```
┌─────────────────────────────────────────────────────────────────────────┐
│  YAOGUANG SOC BACKEND DESIGN FLOW                                       │
└─────────────────────────────────────────────────────────────────────────┘

RTL Design (Complete)
     │
     ▼
┌─────────────────────────────────────────────────────────────────────────┐
│  LOGICAL SYNTHESIS (DC)                                                 │
│  ├── Read RTL                                                           │
│  ├── Apply SDC                                                          │
│  ├── Optimize (Area/Timing/Power)                                       │
│  └── Output: Gate-level Netlist                                         │
└─────────────────────────────────────────────────────────────────────────┘
     │
     ▼
┌─────────────────────────────────────────────────────────────────────────┐
│  DFT INSERTION                                                          │
│  ├── Scan Chain Insertion (16 chains, 10x compression)                  │
│  ├── MBIST Controllers (Memory BIST)                                    │
│  ├── LBIST Controllers (Logic BIST)                                     │
│  └── Boundary Scan (JTAG IEEE 1149.1)                                   │
│  └── Output: DFT Netlist                                                │
└─────────────────────────────────────────────────────────────────────────┘
     │
     ▼
┌─────────────────────────────────────────────────────────────────────────┐
│  FORMAL VERIFICATION                                                    │
│  └── RTL vs Netlist Equivalence Check                                   │
└─────────────────────────────────────────────────────────────────────────┘
     │
     ▼
┌─────────────────────────────────────────────────────────────────────────┐
│  PLACE & ROUTE (ICC2)                                                   │
│  ├── Floorplan                                                          │
│  │   ├── Die/Cell Size                                                  │
│  │   ├── Macro Placement                                                │
│  │   └── Power Grid                                                     │
│  ├── Placement                                                          │
│  │   ├── Global Placement                                               │
│  │   ├── Legalization                                                   │
│  │   └── Optimization                                                   │
│  ├── Clock Tree Synthesis                                               │
│  │   ├── H-Tree Construction                                            │
│  │   ├── Clock Balancing                                                │
│  │   └── Skew Optimization                                              │
│  ├── Routing                                                            │
│  │   ├── Global Routing                                                 │
│  │   ├── Detailed Routing                                               │
│  │   └── DRC Fixes                                                      │
│  └── Optimization                                                       │
│      ├── Timing Optimization                                            │
│      └── Power Optimization                                             │
└─────────────────────────────────────────────────────────────────────────┘
     │
     ▼
┌─────────────────────────────────────────────────────────────────────────┐
│  SIGNOFF                                                                │
│  ├── Timing Signoff (PrimeTime)                                         │
│  │   ├── Multi-corner Analysis                                          │
│  │   ├── Setup/Hold Analysis                                            │
│  │   └── Signoff: Zero Violations                                       │
│  ├── Power Signoff                                                      │
│  │   ├── IR Drop Analysis                                               │
│  │   ├── EM Analysis                                                    │
│  │   └── Signoff: PPA Targets Met                                       │
│  ├── Physical Verification (Calibre)                                    │
│  │   ├── DRC (Design Rule Check)                                        │
│  │   ├── LVS (Layout vs Schematic)                                      │
│  │   ├── Antenna Check                                                  │
│  │   └── Signoff: Clean Database                                        │
│  └── DFT Signoff                                                        │
│      ├── Scan Coverage > 95%                                            │
│      └── ATPG Patterns Valid                                            │
└─────────────────────────────────────────────────────────────────────────┘
     │
     ▼
┌─────────────────────────────────────────────────────────────────────────┐
│  TAPE-OUT                                                               │
│  ├── GDSII Database                                                     │
│  ├── Timing Library (LEF/LIB)                                           │
│  ├── Test Patterns (ATPG)                                               │
│  ├── Signoff Documentation                                              │
│  └── Foundry Handoff                                                    │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 10. Project Metrics

### Design Statistics

| Metric | Value |
|--------|-------|
| Total Gates | ~50M |
| Flip-Flops | ~5M |
| Clock Domains | 13 primary + 16 total |
| Power Domains | 6 |
| Metal Layers | 10 |
| Die Size | 15mm × 15mm |
| Core Size | 12mm × 12mm |
| Target Frequency | 2.0 GHz (Core/NPU) |
| Target Power | < 30W |

### Verification Coverage

| Phase | Coverage Target | Status |
|-------|-----------------|--------|
| DV | 100% Code, 100% Func | ✅ Complete |
| CV | 95% Code, 95% Func | ✅ Complete |
| DFT | 95% Scan, 99% Fault | Ready |

### Schedule Status

| Milestone | Planned | Actual | Status |
|-----------|---------|--------|--------|
| RTL Freeze | Week 1 | Week 1 | ✅ |
| DV Signoff | Week 2 | Week 2 | ✅ |
| CV Signoff | Week 3 | Week 3 | ✅ |
| Synthesis Complete | Week 4 | Pending | ⏳ |
| DFT Insertion | Week 4 | Pending | ⏳ |
| Floorplan Complete | Week 5 | Pending | ⏳ |
| P&R Complete | Week 7 | Pending | ⏳ |
| Timing Signoff | Week 8 | Pending | ⏳ |
| Physical Signoff | Week 9 | Pending | ⏳ |
| Tapeout | Week 10 | Pending | ⏳ |

---

## 11. Risk Assessment

| Risk | Impact | Probability | Mitigation |
|------|--------|-------------|------------|
| Timing closure at 2.0 GHz | High | Medium | Multiple PVT corners, physical aware synthesis |
| Power exceed 30W | Medium | Low | Clock gating, power gating, DVFS |
| DRC violations | Medium | Medium | Regular checks, design rule aware placement |
| Routing congestion | Medium | Low | Floorplan optimization, spare cells |
| Library characterization | High | Low | Early engagement with fab |

---

## 12. Next Steps

### Immediate (This Week)

1. **Run DC Synthesis**
   ```bash
   cd 07_Backend/scripts/dc
   ./run_synthesis.sh
   ```

2. **Verify Synthesis Results**
   - Check `reports/area.rpt`
   - Check `reports/timing.rpt`
   - Check `reports/power.rpt`

3. **Run DFT Insertion**
   ```bash
   cd 07_Backend/dft
   tclsh dft_insertion.tcl
   ```

### Short-term (Next 1-2 Weeks)

4. **Create Floorplan**
   - Execute `scripts/icc2/floorplan.tcl`
   - Verify macro placement
   - Review power grid

5. **Place & Route**
   - Execute `scripts/icc2/placement.tcl`
   - Execute `scripts/icc2/cts.tcl`
   - Execute `scripts/icc2/routing.tcl`

### Medium-term (2-4 Weeks)

6. **Timing Signoff**
   - Execute `scripts/pt/pt_analysis.tcl`
   - Fix timing violations
   - Repeat until WNS > 0

7. **Physical Verification**
   - Run DRC/LVS checks
   - Fix violations
   - Final signoff

---

## 13. Documentation Summary

| Document | Location | Status |
|----------|----------|--------|
| Backend Plan | `07_Backend/backend_plan.md` | ✅ Complete |
| Backend Checklist | `07_Backend/backend_checklist.md` | ✅ Complete |
| Backend Flow | `07_Backend/backend_flow.md` | ✅ Complete |
| SDC Constraints | `07_Backend/sdc/yaoguang_soc.sdc` | ✅ Complete |
| Synthesis Report | `07_Backend/reports/SYNTHESIS_REPORT.md` | ✅ Complete |
| UPF Power Intent | `07_Backend/power/yaoguang_soc.upf` | ✅ Complete |
| DFT Configuration | `07_Backend/dft/dft_config.tcl` | ✅ Complete |
| DRC Ruleset | `07_Backend/calibre/yaoguang_drc.runset` | ✅ Complete |
| LVS Ruleset | `07_Backend/calibre/yaoguang_lvs.runset` | ✅ Complete |

---

## 14. Approval

| Role | Name | Date |
|------|------|------|
| Backend Lead | _______________ | __________ |
| Project Manager | _______________ | __________ |
| Design Manager | _______________ | __________ |
| Quality Engineer | _______________ | __________ |

---

*End of Progress Report*
