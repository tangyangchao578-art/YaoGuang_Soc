# Ethernet控制器设计指南

## 1. 概述

Ethernet控制器支持10G和1G两种速率，支持TSN时间敏感网络。

## 2. 架构要求

| 指标 | 规格 |
|------|------|
| 10G速率 | 10 Gbps (XGMII) |
| 1G速率 | 1 Gbps (RGMII) |
| TSN | 支持 |
| 帧长度 | 9600 bytes max |

## 3. 开发任务

1. 10G PHY接口（6周）
2. 1G PHY接口（4周）
3. MAC层（5周）
4. TSN特性（4周）
5. DMA引擎（4周）
