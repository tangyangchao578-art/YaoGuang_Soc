#ifndef GPIO_HW_H
#define GPIO_HW_H

#include <stdint.h>

#define GPIO_BASE_ADDR  0x40060000

#define GPIO_REG_DATA           0x0000
#define GPIO_REG_DIR            0x0004
#define GPIO_REG_INT_EN         0x0010
#define GPIO_REG_INT_MASK       0x0014
#define GPIO_REG_INT_TYPE       0x0018
#define GPIO_REG_INT_POL        0x001C
#define GPIO_REG_INT_STATUS     0x0020
#define GPIO_REG_INT_CLEAR      0x0024
#define GPIO_REG_DEBOUNCE_EN    0x0030
#define GPIO_REG_DEBOUNCE_CR    0x0034

#define GPIO_INT_TYPE_EDGE      0x00000000
#define GPIO_INT_TYPE_LEVEL     0x00000001
#define GPIO_INT_POL_LOW        0x00000000
#define GPIO_INT_POL_HIGH       0x00000001

void test_gpio(void);

#endif
