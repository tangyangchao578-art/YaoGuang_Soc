#ifndef CAN_HW_H
#define CAN_HW_H

#include <stdint.h>

#define CAN_BASE_ADDR  0x40050000

#define CAN_REG_CR             0x0000
#define CAN_REG_SR             0x0004
#define CAN_REG_BTR            0x0008
#define CAN_REG_BTR_FD         0x000C
#define CAN_REG_TX_ID          0x0100
#define CAN_REG_TX_DLC         0x0104
#define CAN_REG_TX_DATA        0x0108
#define CAN_REG_TX_CR          0x010C
#define CAN_REG_TX_SR          0x0110
#define CAN_REG_RX_ID          0x0200
#define CAN_REG_RX_DLC         0x0204
#define CAN_REG_RX_DATA        0x0208
#define CAN_REG_RX_SR          0x020C
#define CAN_REG_AF_ACR(x)      (0x0300 + (x) * 4)
#define CAN_REG_AF_AMR(x)      (0x0340 + (x) * 4)

#define CAN_CR_FD_ENABLE       0x00000001
#define CAN_CR_ISO             0x00000002
#define CAN_IDE_STD            0x00000000
#define CAN_IDE_EXT            0x00000004
#define CAN_TX_CR_START        0x00000001
#define CAN_TX_SR_SUCCESS      0x00000001
#define CAN_RX_SR_RDY          0x00000001
#define CAN_BTR_BRP(x)         ((x) << 0)
#define CAN_BTR_BRP_MASK       0x0000003F
#define CAN_BTR_TSEG1(x)       ((x) << 6)
#define CAN_BTR_TSEG2(x)       ((x) << 14)
#define CAN_BTR_FD_BRP(x)      ((x) << 0)
#define CAN_BTR_FD_TSEG1(x)    ((x) << 6)
#define CAN_BTR_FD_TSEG2(x)    ((x) << 14)

void test_can(void);

#endif
