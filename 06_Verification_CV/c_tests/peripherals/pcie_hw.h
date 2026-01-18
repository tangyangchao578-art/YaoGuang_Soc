#ifndef PCIE_HW_H
#define PCIE_HW_H

#include <stdint.h>

#define PCIE_BASE_ADDR  0x40020000

#define PCIE_REG_CTRL           0x0000
#define PCIE_REG_STATUS         0x0004
#define PCIE_REG_ENUM_START     0x0010
#define PCIE_REG_ENUM_DONE      0x0014
#define PCIE_REG_ENUM_BUS       0x0018
#define PCIE_REG_ENUM_DEV       0x001C
#define PCIE_REG_ENUM_FUNC      0x0020
#define PCIE_REG_DMA_SRC_L      0x0100
#define PCIE_REG_DMA_SRC_H      0x0104
#define PCIE_REG_DMA_DST_L      0x0108
#define PCIE_REG_DMA_DST_H      0x010C
#define PCIE_REG_DMA_SIZE       0x0110
#define PCIE_REG_DMA_CTRL       0x0114
#define PCIE_REG_DMA_STATUS     0x0118
#define PCIE_REG_INT_STATUS     0x0200
#define PCIE_REG_INT_MASK       0x0204
#define PCIE_REG_INT_CLEAR      0x0208

#define PCIE_CTRL_RESET         0x00000001
#define PCIE_CTRL_LINK_UP       0x00000002
#define PCIE_STATUS_LINK_UP     0x00000001
#define PCIE_DMA_START          0x00000001
#define PCIE_DMA_DONE           0x00000001
#define PCIE_DMA_ERROR          0x00000002
#define PCIE_INT_MSI            0x00000001
#define PCIE_INT_LINK           0x00000002

void test_pcie(void);

#endif
