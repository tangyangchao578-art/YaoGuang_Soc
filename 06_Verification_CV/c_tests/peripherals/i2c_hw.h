#ifndef I2C_HW_H
#define I2C_HW_H

#include <stdint.h>

#define I2C_BASE_ADDR  0x40070000

#define I2C_REG_CR             0x0000
#define I2C_REG_SR             0x0004
#define I2C_REG_ADDR           0x0008
#define I2C_REG_TX             0x000C
#define I2C_REG_RX             0x0010
#define I2C_REG_SCR            0x0014
#define I2C_REG_FIFO_LEVEL     0x0018
#define I2C_REG_INT_STATUS     0x0020
#define I2C_REG_INT_MASK       0x0024
#define I2C_REG_INT_CLEAR      0x0028

#define I2C_CR_ENABLE          0x00000001
#define I2C_CR_MASTER          0x00000002
#define I2C_CR_START           0x00000004
#define I2C_CR_STOP            0x00000008
#define I2C_CR_FAST_MODE       0x00000010
#define I2C_CR_HIGH_SPEED      0x00000020
#define I2C_SR_BUSY            0x00000001
#define I2C_SR_RX_READY        0x00000002
#define I2C_SR_TX_EMPTY        0x00000004
#define I2C_SR_ERROR           0x00000008
#define I2C_INT_TX_EMPTY       0x00000001
#define I2C_INT_RX_FULL        0x00000002
#define I2C_INT_ERROR          0x00000004

void test_i2c(void);

#endif
