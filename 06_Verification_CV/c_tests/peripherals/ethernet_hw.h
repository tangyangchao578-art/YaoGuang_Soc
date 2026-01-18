#ifndef ETHERNET_HW_H
#define ETHERNET_HW_H

#include <stdint.h>

#define ETH_BASE_ADDR  0x40030000

#define ETH_REG_MAC_CR         0x0000
#define ETH_REG_MAC_SR         0x0004
#define ETH_REG_PHY_CR         0x0010
#define ETH_REG_PHY_SR         0x0014
#define ETH_REG_TX_CR          0x0100
#define ETH_REG_TX_DATA        0x0104
#define ETH_REG_RX_STATUS      0x0200
#define ETH_REG_RX_LEN         0x0204
#define ETH_REG_RX_DATA        0x0208
#define ETH_REG_DMA_CR         0x0300
#define ETH_REG_DMA_SR         0x0304

#define ETH_MAC_CR_TX_EN       0x00000001
#define ETH_MAC_CR_RX_EN       0x00000002
#define ETH_MAC_CR_SOFT_RST    0x00000004
#define ETH_PHY_CR_AUTO_NEG    0x00000001
#define ETH_PHY_SR_AN_COMPLETE 0x00000001
#define ETH_PHY_SR_SPEED       0x00000006
#define ETH_PHY_SR_1000M       0x00000002
#define ETH_PHY_SR_100M        0x00000000
#define ETH_PHY_SR_10M         0x00000004
#define ETH_TX_CR_START        0x00000001
#define ETH_TX_CR_TX           0x00000002
#define ETH_RX_STATUS_FRAME_RDY 0x00000001
#define ETH_DMA_CR_RX_START    0x00000001
#define ETH_DMA_CR_TX_START    0x00000002
#define ETH_DMA_SR_RX_BUSY     0x00000001
#define ETH_DMA_SR_TX_BUSY     0x00000002

void test_ethernet(void);

#endif
