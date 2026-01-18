# Crypto Engine Coverage Report

## Test Summary
| Metric | Value |
|--------|-------|
| Total Test Points | 12 |
| P0 Test Points | 10 |
| P1 Test Points | 2 |
| Executed Tests | 12 |
| Passed Tests | 12 |
| Failed Tests | 0 |

## Functional Coverage Details

### Algorithms
| Algorithm | Mode | Coverage |
|-----------|------|----------|
| AES-128 | ECB | 100% |
| AES-128 | CBC | 100% |
| AES-128 | CTR | 100% |
| AES-256 | CBC | 88% |
| SHA-256 | - | 100% |
| SHA-512 | - | 75% |
| RSA-2048 | - | 62% |

### Key Sizes
| Key Size | Coverage |
|----------|----------|
| 128-bit | 100% |
| 192-bit | 88% |
| 256-bit | 75% |

## Performance Metrics
| Test Case | Measured | Target | Status |
|-----------|----------|--------|--------|
| AES-128 Throughput | 2.1 Gbps | 2 Gbps | ✅ Pass |
| SHA-256 Throughput | 1.5 Gbps | 1.5 Gbps | ✅ Pass |
| Latency | 45 cycles | 50 cycles | ✅ Pass |
