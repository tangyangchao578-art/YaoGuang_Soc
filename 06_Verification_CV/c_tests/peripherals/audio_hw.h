#ifndef AUDIO_HW_H
#define AUDIO_HW_H

#include <stdint.h>

#define AUDIO_BASE_ADDR  0x400B0000

#define AUDIO_REG_CR             0x0000
#define AUDIO_REG_SR             0x0004
#define AUDIO_REG_PLAY_CR        0x0010
#define AUDIO_REG_PLAY_SR        0x0014
#define AUDIO_REG_PLAY_FIFO      0x0018
#define AUDIO_REG_CAP_CR         0x0020
#define AUDIO_REG_CAP_SR         0x0024
#define AUDIO_REG_I2S_CR         0x0030
#define AUDIO_REG_VOL_L          0x0040
#define AUDIO_REG_VOL_R          0x0044
#define AUDIO_REG_DITHER_CR      0x0050
#define AUDIO_REG_INT_STATUS     0x0060
#define AUDIO_REG_INT_MASK       0x0064
#define AUDIO_REG_INT_CLEAR      0x0068

#define AUDIO_CR_ENABLE          0x00000001
#define AUDIO_CR_SOFT_RST        0x00000002
#define AUDIO_PLAY_CR_ENABLE     0x00000001
#define AUDIO_CAP_CR_ENABLE      0x00000001
#define AUDIO_I2S_CR_LEFT_ALIGN  0x00000001
#define AUDIO_I2S_CR_RIGHT_ALIGN 0x00000000
#define AUDIO_I2S_CR_16BIT       0x00000000
#define AUDIO_I2S_CR_24BIT       0x00000002
#define AUDIO_I2S_CR_32BIT       0x00000004
#define AUDIO_DITHER_ENABLE      0x00000001
#define AUDIO_INT_PLAY_DONE      0x00000001
#define AUDIO_INT_CAP_RDY        0x00000002

void test_audio(void);

#endif
