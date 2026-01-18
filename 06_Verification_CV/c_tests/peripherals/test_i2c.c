#include "test_framework.h"
#include "i2c_hw.h"

#define I2C_BASE_ADDR  0x40070000

static uint32_t i2c_test_passed = 0;
static uint32_t i2c_test_failed = 0;

static void i2c_reg_write(uint32_t offset, uint32_t value) {
    volatile uint32_t *reg = (volatile uint32_t *)(I2C_BASE_ADDR + offset);
    *reg = value;
}

static uint32_t i2c_reg_read(uint32_t offset) {
    volatile uint32_t *reg = (volatile uint32_t *)(I2C_BASE_ADDR + offset);
    return *reg;
}

static int test_i2c_master_write(void) {
    uint32_t val;
    uint8_t slave_addr = 0x50;
    uint8_t write_data[4] = {0x00, 0x01, 0x02, 0x03};
    
    PRINTF("\n=== Test: I2C Master Write ===\n");
    
    i2c_reg_write(I2C_REG_CR, I2C_CR_MASTER | I2C_CR_START);
    i2c_reg_write(I2C_REG_TX, (slave_addr << 1) | 0x00);
    
    for (int i = 0; i < 4; i++) {
        i2c_reg_write(I2C_REG_TX, write_data[i]);
    }
    
    i2c_reg_write(I2C_REG_CR, I2C_CR_MASTER | I2C_CR_STOP);
    
    delay_ms(10);
    val = i2c_reg_read(I2C_REG_SR);
    
    if (!(val & I2C_SR_BUSY)) {
        PRINTF("[PASS] I2C master write completed\n");
        i2c_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] I2C write in progress or error, sr=0x%08X\n", val);
        i2c_test_failed++;
        return -1;
    }
}

static int test_i2c_master_read(void) {
    uint32_t val;
    uint8_t slave_addr = 0x50;
    
    PRINTF("\n=== Test: I2C Master Read ===\n");
    
    i2c_reg_write(I2C_REG_CR, I2C_CR_MASTER | I2C_CR_START);
    i2c_reg_write(I2C_REG_TX, (slave_addr << 1) | 0x01);
    
    i2c_reg_write(I2C_REG_CR, I2C_CR_MASTER | I2C_CR_STOP);
    
    delay_ms(10);
    val = i2c_reg_read(I2C_REG_SR);
    
    if (!(val & I2C_SR_BUSY)) {
        PRINTF("[PASS] I2C master read configured\n");
        i2c_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] I2C read error, sr=0x%08X\n", val);
        i2c_test_failed++;
        return -1;
    }
}

static int test_i2c_eeprom_access(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: I2C EEPROM Access ===\n");
    
    i2c_reg_write(I2C_REG_ADDR, 0x50);
    i2c_reg_write(I2C_REG_CR, I2C_CR_ENABLE);
    
    val = i2c_reg_read(I2C_REG_CR);
    if (val & I2C_CR_ENABLE) {
        PRINTF("[PASS] I2C enabled for EEPROM access\n");
        i2c_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] I2C not enabled, cr=0x%08X\n", val);
        i2c_test_failed++;
        return -1;
    }
}

static int test_i2c_clock_stretch(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: I2C Clock Stretch ===\n");
    
    i2c_reg_write(I2C_REG_SCR, 0x000000FF);
    
    val = i2c_reg_read(I2C_REG_SCR);
    if ((val & 0x000000FF) == 0x000000FF) {
        PRINTF("[PASS] Clock stretch enabled\n");
        i2c_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Clock stretch configuration error\n");
        i2c_test_failed++;
        return -1;
    }
}

static int test_i2c_speed_mode(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: I2C Speed Mode ===\n");
    
    i2c_reg_write(I2C_REG_CR, I2C_CR_FAST_MODE);
    
    val = i2c_reg_read(I2C_REG_CR);
    if (val & I2C_CR_FAST_MODE) {
        PRINTF("[PASS] Fast mode (400KHz) configured\n");
        i2c_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Speed mode configuration error\n");
        i2c_test_failed++;
        return -1;
    }
}

static int test_i2c_interrupt(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: I2C Interrupt ===\n");
    
    i2c_reg_write(I2C_REG_INT_MASK, 0xFFFFFFFF);
    i2c_reg_write(I2C_REG_INT_CLEAR, 0xFFFFFFFF);
    
    i2c_reg_write(I2C_REG_INT_MASK, I2C_INT_TX_EMPTY | I2C_INT_RX_FULL | I2C_INT_ERROR);
    
    val = i2c_reg_read(I2C_REG_INT_MASK);
    if ((val & (I2C_INT_TX_EMPTY | I2C_INT_RX_FULL | I2C_INT_ERROR)) == 0) {
        PRINTF("[PASS] Interrupt configured\n");
        i2c_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Interrupt configuration error\n");
        i2c_test_failed++;
        return -1;
    }
}

void test_i2c(void) {
    PRINTF("\n");
    PRINTF("========================================\n");
    PRINTF("  I2C Controller Test Suite\n");
    PRINTF("========================================\n");
    
    test_i2c_master_write();
    test_i2c_master_read();
    test_i2c_eeprom_access();
    test_i2c_clock_stretch();
    test_i2c_speed_mode();
    test_i2c_interrupt();
    
    PRINTF("\n========================================\n");
    PRINTF("  I2C Test Results: PASS=%u FAIL=%u\n", 
           i2c_test_passed, i2c_test_failed);
    PRINTF("========================================\n");
}
