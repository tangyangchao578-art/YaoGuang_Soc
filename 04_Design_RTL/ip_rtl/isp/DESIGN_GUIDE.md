# ISP图像信号处理器设计指南

## 1. 概述

ISP负责图像信号处理，支持16+路4K@60fps摄像头输入。

## 2. 架构要求

| 指标 | 规格 |
|------|------|
| 输入通道 | 16+ cameras |
| 分辨率 | 4K @ 60fps |
| 接口 | MIPI CSI-2 v2.0 |
| 处理管线 | Bayer RGB -> RGB -> YUV |

## 3. 处理管线

```
Raw Bayer -> Demosaic -> AWB -> CCM -> Gamma -> Denoise -> sharpen -> YUV -> encode
```

## 4. 开发任务

1. MIPI CSI-2接收器（6周）
2. Demosaic模块（4周）
3. AWB/CCM颜色处理（4周）
4. Gamma和降噪（4周）
5. 输出编码器（3周）
6. 整体集成（3周）
