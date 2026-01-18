#include "test_framework.h"
#include "gpio_hw.h"

#define GPIO_BASE_ADDR  0x40060000

static uint32_t gpio_test_passed = 0;
static uint32_t gpio_test_failed = 0;

static void gpio_reg_write(uint32_t offset, uint32_t value) {
    volatile uint32_t *reg = (volatile uint32_t *)(GPIO_BASE_ADDR + offset);
    *reg = value;
}

static uint32_t gpio_reg_read(uint32_t offset) {
    volatile uint32_t *reg = (volatile uint32_t *)(GPIO_BASE_ADDR + offset);
    return *reg;
}

static int test_gpio_direction(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: GPIO Direction Control ===\n");
    
    gpio_reg_write(GPIO_REG_DIR, 0x00000001);
    val = gpio_reg_read(GPIO_REG_DIR);
    
    if (val == 0x00000001) {
        PRINTF("[PASS] GPIO0 set as output\n");
        gpio_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Direction register error, dir=0x%08X\n", val);
        gpio_test_failed++;
        return -1;
    }
}

static int test_gpio_write(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: GPIO Write ===\n");
    
    gpio_reg_write(GPIO_REG_DIR, 0x0000000F);
    gpio_reg_write(GPIO_REG_DATA, 0x00000005);
    val = gpio_reg_read(GPIO_REG_DATA);
    
    if (val == 0x00000005) {
        PRINTF("[PASS] GPIO write successful, data=0x%02X\n", val);
        gpio_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] GPIO write error, data=0x%08X\n", val);
        gpio_test_failed++;
        return -1;
    }
}

static int test_gpio_read(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: GPIO Read ===\n");
    
    gpio_reg_write(GPIO_REG_DIR, 0x00000000);
    val = gpio_reg_read(GPIO_REG_DATA);
    
    PRINTF("[PASS] GPIO read successful, data=0x%08X\n", val);
    gpio_test_passed++;
    return 0;
}

static int test_gpio_toggle(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: GPIO Toggle ===\n");
    
    gpio_reg_write(GPIO_REG_DIR, 0x00000001);
    gpio_reg_write(GPIO_REG_DATA, 0x00000000);
    
    gpio_reg_write(GPIO_REG_DATA, gpio_reg_read(GPIO_REG_DATA) ^ 0x00000001);
    val = gpio_reg_read(GPIO_REG_DATA);
    
    if (val == 0x00000001) {
        PRINTF("[PASS] GPIO toggle successful\n");
        gpio_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] GPIO toggle error, data=0x%08X\n", val);
        gpio_test_failed++;
        return -1;
    }
}

static int test_gpio_interrupt(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: GPIO Interrupt ===\n");
    
    gpio_reg_write(GPIO_REG_INT_MASK, 0xFFFFFFFF);
    gpio_reg_write(GPIO_REG_INT_CLEAR, 0xFFFFFFFF);
    
    gpio_reg_write(GPIO_REG_INT_TYPE, GPIO_INT_TYPE_EDGE);
    gpio_reg_write(GPIO_REG_INT_POL, GPIO_INT_POL_HIGH);
    gpio_reg_write(GPIO_REG_INT_EN, 0x00000001);
    
    val = gpio_reg_read(GPIO_REG_INT_EN);
    if (val == 0x00000001) {
        PRINTF("[PASS] GPIO interrupt configured\n");
        gpio_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Interrupt configuration error, en=0x%08X\n", val);
        gpio_test_failed++;
        return -1;
    }
}

static int test_gpio_debounce(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: GPIO Debounce ===\n");
    
    gpio_reg_write(GPIO_REG_DEBOUNCE_EN, 0x00000001);
    gpio_reg_write(GPIO_REG_DEBOUNCE_CR, 0x00000064);
    
    val = gpio_reg_read(GPIO_REG_DEBOUNCE_EN);
    if (val == 0x00000001) {
        PRINTF("[PASS] Debounce enabled (10ms)\n");
        gpio_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Debounce configuration error\n");
        gpio_test_failed++;
        return -1;
    }
}

void test_gpio(void) {
    PRINTF("\n");
    PRINTF("========================================\n");
    PRINTF("  GPIO Controller Test Suite\n");
    PRINTF("========================================\n");
    
    test_gpio_direction();
    test_gpio_write();
    test_gpio_read();
    test_gpio_toggle();
    test_gpio_interrupt();
    test_gpio_debounce();
    
    PRINTF("\n========================================\n");
    PRINTF("  GPIO Test Results: PASS=%u FAIL=%u\n", 
           gpio_test_passed, gpio_test_failed);
    PRINTF("========================================\n");
}
