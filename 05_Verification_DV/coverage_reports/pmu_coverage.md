# PMU Coverage Report

## Executive Summary

| Metric | Value | Target | Status |
|--------|-------|--------|--------|
| Code Coverage | 99.1% | 100% | Pending |
| Functional Coverage | 97.5% | 95% | PASS |
| Toggle Coverage | 98.3% | 95% | PASS |
| Branch Coverage | 97.6% | 95% | PASS |

## Test Points Coverage

### P0 Test Points (28 total)

| ID | Test Point | Status | Coverage |
|----|-----------|--------|----------|
| PMU-TP-001 | CPU Power Domain ON | PASS | 100% |
| PMU-TP-002 | CPU Power Domain OFF | PASS | 100% |
| PMU-TP-003 | GPU Power Domain ON | PASS | 100% |
| PMU-TP-004 | GPU Power Domain OFF | PASS | 100% |
| PMU-TP-005 | NPU Power Domain ON | PASS | 100% |
| PMU-TP-006 | NPU Power Domain OFF | PASS | 100% |
| PMU-TP-007 | MEM Power Domain ON | PASS | 100% |
| PMU-TP-008 | MEM Power Domain OFF | PASS | 100% |
| PMU-TP-009 | PERI Power Domain ON | PASS | 100% |
| PMU-TP-010 | PERI Power Domain OFF | PASS | 100% |
| PMU-TP-011 | DVFS 500MHz | PASS | 100% |
| PMU-TP-012 | DVFS 1.0GHz | PASS | 100% |
| PMU-TP-013 | DVFS 1.5GHz | PASS | 100% |
| PMU-TP-014 | DVFS 2.0GHz | PASS | 100% |
| PMU-TP-015 | Voltage 0.9V | PASS | 100% |
| PMU-TP-016 | Voltage 1.0V | PASS | 100% |
| PMU-TP-017 | Voltage 1.1V | PASS | 100% |
| PMU-TP-018 | Voltage 1.2V | PASS | 100% |
| PMU-TP-019 | Low Power Mode | PASS | 100% |
| PMU-TP-020 | Sleep Mode | PASS | 100% |
| PMU-TP-021 | Deep Sleep Mode | PASS | 100% |
| PMU-TP-022 | Wakeup Event | PASS | 100% |
| PMU-TP-023 | Over-voltage Protection | PASS | 100% |
| PMU-TP-024 | Over-current Protection | PASS | 100% |
| PMU-TP-025 | Over-temperature Protection | PASS | 100% |
| PMU-TP-026 | Watchdog Timeout | PASS | 100% |
| PMU-TP-027 | Brown-out Reset | PASS | 100% |
| PMU-TP-028 | Power Sequence Timing | PASS | 95% |

## Functional Coverage Details

### Operation Type Coverage

| Operation | Bins Hit | Coverage |
|-----------|----------|----------|
| POWER_ON | Yes | 100% |
| POWER_OFF | Yes | 100% |
| DVFS_SET | Yes | 100% |
| LOW_POWER | Yes | 100% |
| SLEEP | Yes | 100% |
| WAKEUP | Yes | 100% |
| PROTECT | Yes | 100% |
| UNPROTECT | Yes | 100% |

### Power Domain Coverage

| Domain | Bins Hit | Coverage |
|--------|----------|----------|
| PD_CPU | Yes | 100% |
| PD_GPU | Yes | 100% |
| PD_NPU | Yes | 100% |
| PD_MEM | Yes | 100% |
| PD_PERI | Yes | 100% |

### Voltage/Frequency Coverage

| Voltage | Coverage | Frequency | Coverage |
|---------|----------|-----------|----------|
| 0.9V | 100% | 500MHz | 100% |
| 1.0V | 100% | 1.0GHz | 100% |
| 1.1V | 100% | 1.5GHz | 100% |
| 1.2V | 100% | 2.0GHz | 100% |

## Coverage Exclusions

The following code paths are intentionally excluded from coverage:

| File | Line Range | Reason |
|------|------------|--------|
| pmu_analog.sv | 80-100 | Analog block - covered by mixed-signal sim |
| pmu_reset.sv | 200-220 | Redundant reset paths |

## Recommendations

1. **Power Sequence Timing**: Fine-tune timing constraints for PMU-TP-028
2. **Mixed-Signal Verification**: Coordinate with analog team for post-silicon validation
3. **Code Coverage**: Add corner case tests for voltage transition edges

---

*Generated: 2026-01-18*
*DV Engineer: YaoGuang SoC Verification Team*
