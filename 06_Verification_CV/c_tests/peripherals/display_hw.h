#ifndef DISPLAY_HW_H
#define DISPLAY_HW_H

#include <stdint.h>

#define DISPLAY_BASE_ADDR  0x400A0000

#define DISP_REG_CR              0x0000
#define DISP_REG_STATUS          0x0004
#define DISP_REG_LAYER0_CR       0x0010
#define DISP_REG_LAYER0_ADDR     0x0014
#define DISP_REG_LAYER0_STRIDE   0x0018
#define DISP_REG_LAYER0_SIZE     0x001C
#define DISP_REG_FB_ADDR         0x0100
#define DISP_REG_FB_STRIDE       0x0104
#define DISP_REG_FB_FORMAT       0x0108
#define DISP_REG_HTIMING         0x0200
#define DISP_REG_VTIMING         0x0204
#define DISP_REG_POLARITY        0x0208
#define DISP_REG_DITHER_CR       0x0300
#define DISP_REG_INT_STATUS      0x0400
#define DISP_REG_INT_MASK        0x0404
#define DISP_REG_INT_CLEAR       0x0408

#define DISP_CR_ENABLE           0x00000001
#define DISP_CR_SOFT_RST         0x00000002
#define DISP_LAYER_CR_ENABLE     0x00000001
#define DISP_FMT_RGB888          0x00000000
#define DISP_FMT_RGB565          0x00000001
#define DISP_POL_HSYNC           0x00000001
#define DISP_POL_VSYNC           0x00000002
#define DISP_DITHER_ENABLE       0x00000001
#define DISP_INT_FRM_DONE        0x00000001
#define DISP_INT_UNDERRUN        0x00000002

void test_display(void);

#endif
