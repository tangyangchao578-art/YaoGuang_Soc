# CAN FD Controller Coverage Report

## Test Summary
| Metric | Value |
|--------|-------|
| Total Test Points | 10 |
| P0 Test Points | 8 |
| P1 Test Points | 2 |
| Executed Tests | 10 |
| Passed Tests | 10 |
| Failed Tests | 0 |

## Functional Coverage Details

### Frame Types
| Type | Coverage |
|------|----------|
| Classical CAN | 100% |
| CAN FD Standard | 100% |
| CAN FD Extended | 88% |
| Remote Frame | 75% |

### Data Length Codes
| DLC | Coverage |
|-----|----------|
| 0-8 | 100% |
| 12 | 100% |
| 16 | 100% |
| 20 | 88% |
| 24 | 75% |
| 32 | 62% |

### Bit Rates
| Mode | Coverage |
|------|----------|
| 1 Mbps | 100% |
| 2 Mbps | 100% |
| 5 Mbps | 75% |
| 8 Mbps | 50% |

## Performance Metrics
| Test Case | Measured | Target | Status |
|-----------|----------|--------|--------|
| Nominal Bit Rate | 1 Mbps | 1 Mbps | ✅ Pass |
| Data Bit Rate | 8 Mbps | 8 Mbps | ⚠️ Pending |
| Message Latency | 45 us | 50 us | ✅ Pass |
