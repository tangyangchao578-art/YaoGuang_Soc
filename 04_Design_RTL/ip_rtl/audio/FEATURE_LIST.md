# Audio Module Feature List

## Overview
This document lists all features implemented in the YaoGuang Audio module.

## Version Information
- **Module Version**: 1.0
- **Date**: 2026-01-18
- **Status**: RTL Development

---

## 1. Audio Interfaces

### 1.1 I2S Controller
| Feature | Status | Description |
|---------|--------|-------------|
| Master Mode | Done | I2S controller operates as master |
| Slave Mode | Done | I2S controller operates as slave |
| Standard I2S | Done | Philips I2S format |
| Left Justified | Done | Left justified format |
| Right Justified | Done | Right justified format |
| 16-bit Data | Done | 16-bit audio samples |
| 20-bit Data | Done | 20-bit audio samples |
| 24-bit Data | Done | 24-bit audio samples |
| 32-bit Data | Done | 32-bit audio samples |
| Multi-channel | Done | Up to 8 channels |
| Configurable Sample Rate | Done | 8kHz - 384kHz |
| BCLK Polarity Config | Done | Configurable BCLK polarity |
| LRCLK Polarity Config | Done | Configurable LRCLK polarity |
| MCLK Output | Done | Master clock output |

### 1.2 TDM Controller
| Feature | Status | Description |
|---------|--------|-------------|
| Master Mode | Done | TDM controller operates as master |
| Slave Mode | Done | TDM controller operates as slave |
| TDM128 | Done | 128 BCLK frame format |
| TDM64 | Done | 64 BCLK frame format |
| TDM32 | Done | 32 BCLK frame format |
| TDM16 | Done | 16 BCLK frame format |
| Configurable Slots | Done | 2 - 32 slots |
| Slot Width Config | Done | 8/16/24/32-bit slots |
| Daisy Chain | Done | Multi-chip cascading |
| FS Polarity Config | Done | Frame sync polarity |
| BCLK Polarity Config | Done | Bit clock polarity |

### 1.3 PDM Controller
| Feature | Status | Description |
|---------|--------|-------------|
| MEMS Mic Interface | Done | PDM microphone interface |
| 64x Oversampling | Done | 64x decimation |
| 128x Oversampling | Done | 128x decimation |
| 256x Oversampling | Done | 256x decimation |
| Stereo Support | Done | 2-channel stereo |
| Quad Support | Done | 4-channel quad |
| High-pass Filter | Done | DC offset removal |
| Low-pass Filter | Done | Anti-aliasing filter |
| CIC Decimation | Done | Cascaded integrator-comb filter |

### 1.4 SPDIF Controller
| Feature | Status | Description |
|---------|--------|-------------|
| AES3 Compliance | Done | AES3/IEC60958 standard |
| Linear PCM | Done | PCM audio support |
| BMC Encoding | Done | Biphase mark code encoding |
| Jitter Attenuation | Done | Built-in jitter cleaner |
| TX Path | Done | SPDIF transmitter |
| RX Path | Done | SPDIF receiver |
| Status Bits | Done | Channel status bits |
| User Data | Done | User data channel |

---

## 2. Audio Processing

### 2.1 Audio DSP
| Feature | Status | Description |
|---------|--------|-------------|
| Harvard Architecture | Done | Separate instruction/data memory |
| 4 MAC Units | Done | Parallel multiply-accumulate |
| 200 MHz Clock | Done | DSP clock frequency |
| 1.6 GMAC/s | Done | Peak performance |
| 4KB I-Cache | Done | Instruction cache |
| 16KB D-Cache | Done | Data cache |
| 32-bit Fixed Point | Done | Fixed point arithmetic |
| 32-bit Float | Done | Floating point support |
| Branch Support | Done | Conditional branches |
| Jump Support | Done | Unconditional jumps |

### 2.2 Sample Rate Converter
| Feature | Status | Description |
|---------|--------|-------------|
| Asynchronous SRC | Done | Independent input/output rates |
| Synchronous SRC | Done | Integer ratio conversion |
| 8kHz - 384kHz Input | Done | Wide input range |
| 8kHz - 384kHz Output | Done | Wide output range |
| 140dB SNR | Done | High quality conversion |
| Polyphase FIR | Done | Multi-phase interpolation |
| Variable Ratio | Done | Configurable rate ratio |
| Bypass Mode | Done | Pass-through mode |

### 2.3 Volume Control
| Feature | Status | Description |
|---------|--------|-------------|
| Master Volume | Done | Master volume control |
| Per-channel Volume | Done | Individual channel gain |
| -100dB to +12dB | Done | Wide gain range |
| 0.5dB Steps | Done | Fine gain control |
| Soft Mute | Done | Gradual mute |
| Soft Clip | Done | Programmable clipper |
| Volume Ramping | Done | Smooth transitions |
| Overflow Protection | Done | Anti-clipping |

### 2.4 Equalizer
| Feature | Status | Description |
|---------|--------|-------------|
| 10-band EQ | Pending | 10 parametric bands |
| Peak/Notch Filter | Pending | Peak filter type |
| Low-shelf Filter | Pending | Low frequency shelf |
| High-shelf Filter | Pending | High frequency shelf |
| All-pass Filter | Pending | Phase control |
| Frequency Range | Pending | 20Hz - 20kHz |
| Gain Range | Pending | -12dB to +12dB |
| Q-factor Config | Pending | Adjustable resonance |

### 2.5 Dynamic Range Compressor
| Feature | Status | Description |
|---------|--------|-------------|
| Threshold Control | Pending | -60dBFS to 0dBFS |
| Ratio Control | Pending | 1:1 to ∞:1 |
| Attack Time | Pending | 0.1ms - 100ms |
| Release Time | Pending | 10ms - 1000ms |
| Hard Knee | Pending | Hard threshold |
| Soft Knee | Pending | Soft threshold |
| Make-up Gain | Pending | Auto make-up |

---

## 3. System Features

### 3.1 Clock & Reset
| Feature | Status | Description |
|---------|--------|-------------|
| APB Interface | Done | Register access |
| AXI-Stream TX | Done | Audio data output |
| AXI-Stream RX | Done | Audio data input |
| Clock Gating | Done | Dynamic clock control |
| Reset Domains | Done | Multiple reset domains |

### 3.2 Interrupts
| Feature | Status | Description |
|---------|--------|-------------|
| TX Complete | Done | Transmission done |
| RX Ready | Done | Data received |
| Error Interrupt | Done | Error conditions |
| DSP Interrupt | Done | DSP events |
| Maskable IRQs | Done | Configurable masks |

---

## 4. Safety Features

### 4.1 Functional Safety
| Feature | Status | Description |
|---------|--------|-------------|
| ECC Protection | Pending | Memory error detection |
| Parity Check | Pending | Data path parity |
| Watchdog Timer | Pending | DSP watchdog |
| Register Redundancy | Pending | Critical register duplicate |
| Loopback Test | Pending | Audio loopback test |

---

## 5. Performance Metrics

### 5.1 Timing
| Metric | Target | Status |
|--------|--------|--------|
| Setup Time | > 10ns | TBD |
| Hold Time | > 5ns | TBD |
| Clock-to-Q | < 2ns | TBD |

### 5.2 Area
| Component | Gate Count | Status |
|-----------|------------|--------|
| I2S Controller | ~2K | Done |
| TDM Controller | ~3K | Done |
| PDM Controller | ~4K | Done |
| SPDIF Controller | ~3K | Done |
| Audio DSP | ~50K | Done |
| Volume Control | ~2K | Done |
| SRC | ~8K | Done |
| Total | ~72K | TBD |

### 5.3 Power
| Mode | Power | Status |
|------|-------|--------|
| Active | ~83mW | TBD |
| Idle | ~10mW | TBD |
| Standby | ~2mW | TBD |
| Power Down | ~0.1mW | TBD |

---

## 6. Verification Status

### 6.1 Simulation
| Test | Coverage | Status |
|------|----------|--------|
| I2S TX/RX | 100% | Done |
| TDM TX/RX | 100% | Done |
| PDM to PCM | 90% | In Progress |
| SPDIF TX/RX | 85% | In Progress |
| DSP Instructions | 75% | In Progress |
| SRC Algorithm | 80% | In Progress |
| Volume Control | 100% | Done |

### 6.2 Emulation
| Test | Status |
|------|--------|
| Boot Sequence | Pending |
| Multi-protocol | Pending |
| Power Cycle | Pending |

---

## 7. Known Issues

| ID | Description | Severity | Status |
|----|-------------|----------|--------|
| AUD-001 | PDM CIC filter coefficient loading | Low | Workaround |
| AUD-002 | DSP cache miss penalty | Medium | Optimization |
| AUD-003 | SRC async mode timing | Low | TBD |

---

## 8. Change Log

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2026-01-18 | RTL Team | Initial RTL version |
| 0.9 | 2026-01-15 | Arch Team | Architecture freeze |
| 0.8 | 2026-01-10 | Arch Team | Feature definition |
