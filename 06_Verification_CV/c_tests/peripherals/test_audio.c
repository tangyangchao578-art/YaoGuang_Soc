#include "test_framework.h"
#include "audio_hw.h"

#define AUDIO_BASE_ADDR  0x400B0000

static uint32_t audio_test_passed = 0;
static uint32_t audio_test_failed = 0;

static void audio_reg_write(uint32_t offset, uint32_t value) {
    volatile uint32_t *reg = (volatile uint32_t *)(AUDIO_BASE_ADDR + offset);
    *reg = value;
}

static uint32_t audio_reg_read(uint32_t offset) {
    volatile uint32_t *reg = (volatile uint32_t *)(AUDIO_BASE_ADDR + offset);
    return *reg;
}

static int test_audio_i2s_init(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: Audio I2S Initialization ===\n");
    
    audio_reg_write(AUDIO_REG_CR, AUDIO_CR_SOFT_RST);
    delay_ms(10);
    audio_reg_write(AUDIO_REG_CR, AUDIO_CR_ENABLE);
    
    val = audio_reg_read(AUDIO_REG_CR);
    if (val & AUDIO_CR_ENABLE) {
        PRINTF("[PASS] Audio engine initialized\n");
        audio_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Audio initialization error, cr=0x%08X\n", val);
        audio_test_failed++;
        return -1;
    }
}

static int test_audio_playback(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: Audio Playback ===\n");
    
    audio_reg_write(AUDIO_REG_PLAY_CR, AUDIO_PLAY_CR_ENABLE);
    audio_reg_write(AUDIO_REG_PLAY_SR, 48000);
    audio_reg_write(AUDIO_REG_PLAY_FIFO, 0x00000001);
    
    val = audio_reg_read(AUDIO_REG_PLAY_CR);
    if (val & AUDIO_PLAY_CR_ENABLE) {
        PRINTF("[PASS] Audio playback configured (48KHz)\n");
        audio_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Playback configuration error\n");
        audio_test_failed++;
        return -1;
    }
}

static int test_audio_capture(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: Audio Capture ===\n");
    
    audio_reg_write(AUDIO_REG_CAP_CR, AUDIO_CAP_CR_ENABLE);
    audio_reg_write(AUDIO_REG_CAP_SR, 48000);
    
    val = audio_reg_read(AUDIO_REG_CAP_CR);
    if (val & AUDIO_CAP_CR_ENABLE) {
        PRINTF("[PASS] Audio capture configured (48KHz)\n");
        audio_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Capture configuration error\n");
        audio_test_failed++;
        return -1;
    }
}

static int test_audio_sample_rate(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: Sample Rate Configuration ===\n");
    
    audio_reg_write(AUDIO_REG_SR, 44100);
    val = audio_reg_read(AUDIO_REG_SR);
    
    if (val == 44100) {
        PRINTF("[PASS] Sample rate configured (44.1KHz)\n");
        audio_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Sample rate configuration error\n");
        audio_test_failed++;
        return -1;
    }
}

static int test_audio_i2s_format(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: I2S Format Configuration ===\n");
    
    audio_reg_write(AUDIO_REG_I2S_CR, AUDIO_I2S_CR_LEFT_ALIGN | AUDIO_I2S_CR_24BIT);
    
    val = audio_reg_read(AUDIO_REG_I2S_CR);
    if ((val & (AUDIO_I2S_CR_LEFT_ALIGN | AUDIO_I2S_CR_24BIT)) == 
        (AUDIO_I2S_CR_LEFT_ALIGN | AUDIO_I2S_CR_24BIT)) {
        PRINTF("[PASS] I2S format: left-aligned, 24-bit\n");
        audio_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] I2S format configuration error\n");
        audio_test_failed++;
        return -1;
    }
}

static int test_audio_volume(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: Volume Control ===\n");
    
    audio_reg_write(AUDIO_REG_VOL_L, 0x80);
    audio_reg_write(AUDIO_REG_VOL_R, 0x80);
    
    val = audio_reg_read(AUDIO_REG_VOL_L);
    if (val == 0x80) {
        PRINTF("[PASS] Volume configured (L=0x%02X, R=0x%02X)\n", 
               val, audio_reg_read(AUDIO_REG_VOL_R));
        audio_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Volume configuration error\n");
        audio_test_failed++;
        return -1;
    }
}

static int test_audio_dither(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: Dither Configuration ===\n");
    
    audio_reg_write(AUDIO_REG_DITHER_CR, AUDIO_DITHER_ENABLE);
    
    val = audio_reg_read(AUDIO_REG_DITHER_CR);
    if (val & AUDIO_DITHER_ENABLE) {
        PRINTF("[PASS] Dithering enabled\n");
        audio_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Dither configuration error\n");
        audio_test_failed++;
        return -1;
    }
}

static int test_audio_interrupt(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: Audio Interrupt ===\n");
    
    audio_reg_write(AUDIO_REG_INT_MASK, 0xFFFFFFFF);
    audio_reg_write(AUDIO_REG_INT_CLEAR, 0xFFFFFFFF);
    
    audio_reg_write(AUDIO_REG_INT_MASK, AUDIO_INT_PLAY_DONE | AUDIO_INT_CAP_RDY);
    
    val = audio_reg_read(AUDIO_REG_INT_MASK);
    if ((val & (AUDIO_INT_PLAY_DONE | AUDIO_INT_CAP_RDY)) == 0) {
        PRINTF("[PASS] Audio interrupt configured\n");
        audio_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Interrupt configuration error\n");
        audio_test_failed++;
        return -1;
    }
}

void test_audio(void) {
    PRINTF("\n");
    PRINTF("========================================\n");
    PRINTF("  Audio Controller Test Suite\n");
    PRINTF("========================================\n");
    
    test_audio_i2s_init();
    test_audio_playback();
    test_audio_capture();
    test_audio_sample_rate();
    test_audio_i2s_format();
    test_audio_volume();
    test_audio_dither();
    test_audio_interrupt();
    
    PRINTF("\n========================================\n");
    PRINTF("  Audio Test Results: PASS=%u FAIL=%u\n", 
           audio_test_passed, audio_test_failed);
    PRINTF("========================================\n");
}
