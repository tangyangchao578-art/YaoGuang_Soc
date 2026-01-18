#include "test_framework.h"
#include "display_hw.h"

#define DISPLAY_BASE_ADDR  0x400A0000

static uint32_t display_test_passed = 0;
static uint32_t display_test_failed = 0;

static void display_reg_write(uint32_t offset, uint32_t value) {
    volatile uint32_t *reg = (volatile uint32_t *)(DISPLAY_BASE_ADDR + offset);
    *reg = value;
}

static uint32_t display_reg_read(uint32_t offset) {
    volatile uint32_t *reg = (volatile uint32_t *)(DISPLAY_BASE_ADDR + offset);
    return *reg;
}

static int test_display_init(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: Display Engine Initialization ===\n");
    
    display_reg_write(DISP_REG_CR, DISP_CR_SOFT_RST);
    delay_ms(10);
    display_reg_write(DISP_REG_CR, DISP_CR_ENABLE);
    
    val = display_reg_read(DISP_REG_CR);
    if (val & DISP_CR_ENABLE) {
        PRINTF("[PASS] Display engine initialized\n");
        display_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Display initialization error, cr=0x%08X\n", val);
        display_test_failed++;
        return -1;
    }
}

static int test_display_layer_config(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: Display Layer Configuration ===\n");
    
    display_reg_write(DISP_REG_LAYER0_CR, DISP_LAYER_CR_ENABLE);
    display_reg_write(DISP_REG_LAYER0_STRIDE, 0x00000780);
    display_reg_write(DISP_REG_LAYER0_ADDR, 0x90000000);
    display_reg_write(DISP_REG_LAYER0_SIZE, (1080 << 16) | 1920);
    
    val = display_reg_read(DISP_REG_LAYER0_CR);
    if (val & DISP_LAYER_CR_ENABLE) {
        PRINTF("[PASS] Layer 0 configured (1920x1080)\n");
        display_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Layer configuration error, layer_cr=0x%08X\n", val);
        display_test_failed++;
        return -1;
    }
}

static int test_display_framebuffer(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: Framebuffer Configuration ===\n");
    
    display_reg_write(DISP_REG_FB_ADDR, 0x90000000);
    display_reg_write(DISP_REG_FB_STRIDE, 0x00000780);
    display_reg_write(DISP_REG_FB_FORMAT, DISP_FMT_RGB888);
    
    val = display_reg_read(DISP_REG_FB_ADDR);
    if (val == 0x90000000) {
        PRINTF("[PASS] Framebuffer configured at 0x%08X\n", val);
        display_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Framebuffer configuration error\n");
        display_test_failed++;
        return -1;
    }
}

static int test_display_timing(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: Display Timing Configuration ===\n");
    
    display_reg_write(DISP_REG_HTIMING, (640 << 16) | 48);
    display_reg_write(DISP_REG_VTIMING, (480 << 16) | 10);
    display_reg_write(DISP_REG_POLARITY, DISP_POL_HSYNC | DISP_POL_VSYNC);
    
    val = display_reg_read(DISP_REG_HTIMING);
    if ((val & 0xFFFF) == 48) {
        PRINTF("[PASS] Display timing configured (VGA 640x480)\n");
        display_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Timing configuration error\n");
        display_test_failed++;
        return -1;
    }
}

static int test_display_dithering(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: Display Dithering ===\n");
    
    display_reg_write(DISP_REG_DITHER_CR, DISP_DITHER_ENABLE);
    
    val = display_reg_read(DISP_REG_DITHER_CR);
    if (val & DISP_DITHER_ENABLE) {
        PRINTF("[PASS] Dithering enabled\n");
        display_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Dithering configuration error\n");
        display_test_failed++;
        return -1;
    }
}

static int test_display_interrupt(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: Display Interrupt ===\n");
    
    display_reg_write(DISP_REG_INT_MASK, 0xFFFFFFFF);
    display_reg_write(DISP_REG_INT_CLEAR, 0xFFFFFFFF);
    
    display_reg_write(DISP_REG_INT_MASK, DISP_INT_FRM_DONE | DISP_INT_UNDERRUN);
    
    val = display_reg_read(DISP_REG_INT_MASK);
    if ((val & (DISP_INT_FRM_DONE | DISP_INT_UNDERRUN)) == 0) {
        PRINTF("[PASS] Display interrupt configured\n");
        display_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Interrupt configuration error\n");
        display_test_failed++;
        return -1;
    }
}

void test_display(void) {
    PRINTF("\n");
    PRINTF("========================================\n");
    PRINTF("  Display Controller Test Suite\n");
    PRINTF("========================================\n");
    
    test_display_init();
    test_display_layer_config();
    test_display_framebuffer();
    test_display_timing();
    test_display_dithering();
    test_display_interrupt();
    
    PRINTF("\n========================================\n");
    PRINTF("  Display Test Results: PASS=%u FAIL=%u\n", 
           display_test_passed, display_test_failed);
    PRINTF("========================================\n");
}
