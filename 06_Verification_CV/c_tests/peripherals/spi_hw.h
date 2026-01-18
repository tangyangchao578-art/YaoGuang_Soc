#ifndef SPI_HW_H
#define SPI_HW_H

#include <stdint.h>

#define SPI_BASE_ADDR  0x40080000

#define SPI_REG_CR             0x0000
#define SPI_REG_SR             0x0004
#define SPI_REG_TX             0x0008
#define SPI_REG_RX             0x000C
#define SPI_REG_BAUD           0x0010
#define SPI_REG_FIFO_LEVEL     0x0014
#define SPI_REG_FCR            0x0018
#define SPI_REG_INT_STATUS     0x0020
#define SPI_REG_INT_MASK       0x0024
#define SPI_REG_INT_CLEAR      0x0028

#define SPI_CR_ENABLE          0x00000001
#define SPI_CR_MASTER          0x00000002
#define SPI_CR_SLAVE           0x00000000
#define SPI_CR_START           0x00000004
#define SPI_CR_CPOL            0x00000008
#define SPI_CR_CPHA            0x00000010
#define SPI_CR_FLASH_MODE      0x00000020
#define SPI_SR_RX_READY        0x00000001
#define SPI_SR_TX_EMPTY        0x00000002
#define SPI_SR_BUSY            0x00000004
#define SPI_FCR_CS_ACTIVE      0x00000001
#define SPI_INT_TX_EMPTY       0x00000001
#define SPI_INT_RX_FULL        0x00000002
#define SPI_INT_ERR            0x00000004

void test_spi(void);

#endif
