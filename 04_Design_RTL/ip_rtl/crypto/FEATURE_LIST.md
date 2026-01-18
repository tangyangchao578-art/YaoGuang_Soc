# Crypto Module Feature List

## Module Overview
- **Module Name**: crypto_top
- **Category**: Security / Cryptography
- **Technology**: CMOS 28nm
- **Version**: 1.0
- **Author**: YaoGuang Team
- **Date**: 2026-01-18

## Supported Features

### 1. Symmetric Encryption

#### AES Engine
| Feature | Support | Description |
|---------|---------|-------------|
| AES-128 | Yes | 128-bit key encryption |
| AES-192 | Yes | 192-bit key encryption |
| AES-256 | Yes | 256-bit key encryption |
| ECB Mode | Yes | Electronic Codebook mode |
| CBC Mode | Yes | Cipher Block Chaining mode |
| CFB Mode | Yes | Cipher Feedback mode |
| CTR Mode | Yes | Counter mode |
| GCM Mode | Yes | Galois/Counter Mode with authentication |

#### SM4 Engine
| Feature | Support | Description |
|---------|---------|-------------|
| SM4-ECB | Yes | SM4 Electronic Codebook mode |
| SM4-CBC | Yes | SM4 Cipher Block Chaining mode |
| SM4-CTR | Yes | SM4 Counter mode |

### 2. Hash Functions

#### SHA-2 Family
| Feature | Support | Description |
|---------|---------|-------------|
| SHA-224 | Yes | 224-bit hash output |
| SHA-256 | Yes | 256-bit hash output |
| SHA-384 | Yes | 384-bit hash output |
| SHA-512 | Yes | 512-bit hash output |
| HMAC-SHA | Yes | Hash-based Message Authentication Code |

#### SHA-3 Family
| Feature | Support | Description |
|---------|---------|-------------|
| SHA3-224 | Yes | 224-bit hash output |
| SHA3-256 | Yes | 256-bit hash output |
| SHA3-384 | Yes | 384-bit hash output |
| SHA3-512 | Yes | 512-bit hash output |

#### SM3
| Feature | Support | Description |
|---------|---------|-------------|
| SM3 | Yes | 256-bit hash output (Chinese standard) |

### 3. Asymmetric Encryption

#### RSA Engine
| Feature | Support | Description |
|---------|---------|-------------|
| RSA-1024 | Yes | 1024-bit key operations |
| RSA-2048 | Yes | 2048-bit key operations |
| RSA-4096 | Yes | 4096-bit key operations |
| CRT Mode | Yes | Chinese Remainder Theorem acceleration |
| PKCS#1 v1.5 | Yes | RSA padding scheme |
| PSS | Yes | Probabilistic Signature Scheme |

#### ECC Engine
| Feature | Support | Description |
|---------|---------|-------------|
| NIST P-256 | Yes | P-256 curve operations |
| NIST P-384 | Yes | P-384 curve operations |
| NIST P-521 | Yes | P-521 curve operations |
| secp256k1 | Yes | Bitcoin curve support |
| ECDSA | Yes | Elliptic Curve DSA |
| ECDH | Yes | Elliptic Curve Diffie-Hellman |

#### SM2 Engine
| Feature | Support | Description |
|---------|---------|-------------|
| SM2-Signature | Yes | SM2 digital signature |
| SM2-Encryption | Yes | SM2 public key encryption |
| SM2-KeyExchange | Yes | SM2 key exchange protocol |

### 4. Random Number Generation

| Feature | Support | Description |
|---------|---------|-------------|
| TRNG | Yes | True Random Number Generator |
| NIST SP 800-90B | Yes | Entropy source compliance |
| DRBG | Yes | Deterministic Random Bit Generator |
| Health Test | Yes | Online entropy health monitoring |

### 5. Key Management

| Feature | Support | Description |
|---------|---------|-------------|
| Secure Key Storage | Yes | Hardware secure key vault |
| Key Derivation | Yes | HKDF, PBKDF2, SMKDF support |
| Key Wrapping | Yes | Key encryption for storage |
| Key Destruction | Yes | Secure key erasure |
| Master Key | Yes | Hardware root key storage |

### 6. Secure Boot Support

| Feature | Support | Description |
|---------|---------|-------------|
| Image Authentication | Yes | RSA/ECDSA signature verification |
| Image Decryption | Yes | AES-GCM decryption support |
| Secure Boot Chain | Yes | Multi-stage boot verification |
| Anti-rollback | Yes | Version counter for rollback protection |

### 7. Security Features

| Feature | Support | Description |
|---------|---------|-------------|
| Fault Injection Protection | Yes | Redundant computation |
| Side Channel Protection | Yes | Constant-time implementations |
| Access Control | Yes | Multi-level privilege support |
| Tamper Detection | Yes | Voltage/temperature monitoring |

## Performance Specifications

### Encryption Performance
| Algorithm | Mode | Throughput | Latency |
|-----------|------|------------|---------|
| AES-256 | GCM | 1.6 GB/s | 14 cycles |
| AES-128 | CBC | 1.8 GB/s | 10 cycles |
| SM4 | CBC | 800 MB/s | 32 cycles |

### Hash Performance
| Algorithm | Throughput | Latency |
|-----------|------------|---------|
| SHA-256 | 800 MB/s | 64 cycles |
| SHA-512 | 1.2 GB/s | 80 cycles |
| SHA3-256 | 600 MB/s | 24 rounds |
| SM3 | 800 MB/s | 64 cycles |

### Asymmetric Performance
| Algorithm | Operation | Time |
|-----------|-----------|------|
| RSA-2048 | Sign | < 10 ms |
| RSA-2048 | Verify | < 2 ms |
| ECC P-256 | Point Multiply | < 0.5 ms |
| SM2 | Sign | < 1 ms |

## Power Specifications

| State | Power | Description |
|-------|-------|-------------|
| Active (Peak) | < 500 mW | All engines active |
| Active (Typical) | < 300 mW | Single engine typical load |
| Standby | < 10 mW | Clock gated |
| Shutdown | < 1 mW | Power gated |

## Interface Specifications

### APB Interface
| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| pclk | 1 | Input | APB clock |
| presetn | 1 | Input | APB reset (active low) |
| paddr | 12 | Input | APB address |
| pwdata | 32 | Input | APB write data |
| prdata | 32 | Output | APB read data |
| pwrite | 1 | Input | Write enable |
| psel | 1 | Input | Slave select |
| penable | 1 | Input | Enable |
| pready | 1 | Output | Ready |

### AXI4-Stream Interface
| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| axis_tvalid | 1 | Input/Output | Valid |
| axis_tready | 1 | Input/Output | Ready |
| axis_tdata | 128 | Input/Output | Data |
| axis_tlast | 1 | Input/Output | Last beat |

### Interrupt Interface
| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| crypto_intr | 1 | Output | Crypto interrupt |

## Register Map

### Offset 0x00 - Control Register
| Bits | Name | Access | Description |
|------|------|--------|-------------|
| [0] | enable | RW | Crypto module enable |
| [1] | clkgate | RW | Clock gate control |
| [8:2] | reserved | RO | Reserved |
| [9] | done | RC | Operation complete |
| [10] | error | RC | Error flag |
| [31:11] | reserved | RO | Reserved |

### Offset 0x04 - Status Register
| Bits | Name | Access | Description |
|------|------|--------|-------------|
| [0] | busy | RO | Engine busy |
| [1] | trng_rdy | RO | TRNG ready |
| [2] | key_ready | RO | Key storage ready |
| [31:3] | reserved | RO | Reserved |

### Offset 0x08 - Key ID Register
| Bits | Name | Access | Description |
|------|------|--------|-------------|
| [7:0] | key_id | RW | Key identifier |
| [31:8] | reserved | RO | Reserved |

### Offset 0x0C - Algorithm Select Register
| Bits | Name | Access | Description |
|------|------|--------|-------------|
| [3:0] | algo | RW | Algorithm select |
| [7:4] | mode | RW | Mode select |
| [31:8] | reserved | RO | Reserved |

### Offset 0x10 - Length Register
| Bits | Name | Access | Description |
|------|------|--------|-------------|
| [31:0] | length | RW | Data length in bytes |

### Offset 0x14 - Start Register
| Bits | Name | Access | Description |
|------|------|--------|-------------|
| [0] | start | WO | Start operation |
| [31:1] | reserved | RO | Reserved |

## Synthesis Targets

| Parameter | Value |
|-----------|-------|
| Frequency | 200 MHz (crypto_clk) |
| Technology | CMOS 28nm |
| Area | ~ 0.96 mm² |
| Gates | ~ 768 K gates |

## Verification Status

| Verification Level | Status | Coverage |
|--------------------|--------|----------|
| Block Level | Pending | - |
| Sub-system Level | Pending | - |
| SoC Level | Pending | - |
| Formal Verification | Pending | - |

## Compliance

| Standard | Status |
|----------|--------|
| ARM TrustZone | Compatible |
| RISC-V Crypto Extensions | Compatible |
| NIST FIPS 180-4 | Compliant |
| NIST FIPS 197 | Compliant |
| ISO 26262 ASIL-D | Target |
| GM/T 0054-2018 | Compliant |
