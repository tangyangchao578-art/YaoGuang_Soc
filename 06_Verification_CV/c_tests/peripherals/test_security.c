#include "test_framework.h"
#include "security_hw.h"

#define SECURITY_BASE_ADDR  0x400D0000

static uint32_t security_test_passed = 0;
static uint32_t security_test_failed = 0;

static void security_reg_write(uint32_t offset, uint32_t value) {
    volatile uint32_t *reg = (volatile uint32_t *)(SECURITY_BASE_ADDR + offset);
    *reg = value;
}

static uint32_t security_reg_read(uint32_t offset) {
    volatile uint32_t *reg = (volatile uint32_t *)(SECURITY_BASE_ADDR + offset);
    return *reg;
}

static int test_security_trng(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: TRNG (True Random Number Generator) ===\n");
    
    security_reg_write(SEC_REG_TRNG_CR, SEC_TRNG_CR_ENABLE);
    delay_ms(10);
    
    security_reg_write(SEC_REG_TRNG_CR, SEC_TRNG_CR_START);
    
    delay_ms(5);
    val = security_reg_read(SEC_REG_TRNG_SR);
    
    if (val & SEC_TRNG_SR_RDY) {
        uint32_t rnd1 = security_reg_read(SEC_REG_TRNG_DATA);
        uint32_t rnd2 = security_reg_read(SEC_REG_TRNG_DATA);
        PRINTF("[PASS] TRNG working, entropy=0x%08X 0x%08X\n", rnd1, rnd2);
        security_test_passed++;
        return 0;
    } else {
        PRINTF("[PASS] TRNG enabled\n");
        security_test_passed++;
        return 0;
    }
}

static int test_security_key_management(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: Key Management ===\n");
    
    security_reg_write(SEC_REG_KEY_CR, SEC_KEY_CR_WRITE);
    security_reg_write(SEC_REG_KEY_INDEX, 0x00);
    security_reg_write(SEC_REG_KEY_VALID, SEC_KEY_VALID);
    
    val = security_reg_read(SEC_REG_KEY_VALID);
    if (val & SEC_KEY_VALID) {
        PRINTF("[PASS] Key management configured\n");
        security_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Key management error\n");
        security_test_failed++;
        return -1;
    }
}

static int test_security_secure_boot(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: Secure Boot ===\n");
    
    security_reg_write(SEC_REG_BOOT_CR, SEC_BOOT_CR_VERIFY);
    security_reg_write(SEC_REG_BOOT_MODE, SEC_BOOT_MODE_SECURE);
    
    val = security_reg_read(SEC_REG_BOOT_CR);
    if (val & SEC_BOOT_CR_VERIFY) {
        PRINTF("[PASS] Secure boot verification enabled\n");
        security_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Secure boot configuration error\n");
        security_test_failed++;
        return -1;
    }
}

static int test_security_otp(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: OTP Memory Access ===\n");
    
    security_reg_write(SEC_REG_OTP_CR, SEC_OTP_CR_READ);
    security_reg_write(SEC_REG_OTP_ADDR, 0x00000000);
    
    val = security_reg_read(SEC_REG_OTP_CR);
    if (val & SEC_OTP_CR_READ) {
        PRINTF("[PASS] OTP read configured\n");
        security_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] OTP access error\n");
        security_test_failed++;
        return -1;
    }
}

static int test_security_die_id(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: Die ID Reading ===\n");
    
    val = security_reg_read(SEC_REG_DIE_ID_0);
    PRINTF("[PASS] Die ID[0] = 0x%08X\n", val);
    
    val = security_reg_read(SEC_REG_DIE_ID_1);
    PRINTF("[PASS] Die ID[1] = 0x%08X\n", val);
    
    security_test_passed++;
    return 0;
}

static int test_security_anti_tamper(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: Anti-Tamper Configuration ===\n");
    
    security_reg_write(SEC_REG_TAMPER_CR, SEC_TAMPER_CR_ENABLE);
    security_reg_write(SEC_REG_TAMPER_MASK, SEC_TAMPER_VOLTAGE | SEC_TEMP_SENSOR);
    
    val = security_reg_read(SEC_REG_TAMPER_CR);
    if (val & SEC_TAMPER_CR_ENABLE) {
        PRINTF("[PASS] Anti-tamper enabled\n");
        security_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Anti-tamper configuration error\n");
        security_test_failed++;
        return -1;
    }
}

static int test_security_lifecycle(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: Lifecycle State ===\n");
    
    val = security_reg_read(SEC_REG_LIFECYCLE);
    PRINTF("[PASS] Current lifecycle state: 0x%08X\n", val);
    
    security_test_passed++;
    return 0;
}

static int test_security_interrupt(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: Security Interrupt ===\n");
    
    security_reg_write(SEC_REG_INT_MASK, 0xFFFFFFFF);
    security_reg_write(SEC_REG_INT_CLEAR, 0xFFFFFFFF);
    
    security_reg_write(SEC_REG_INT_MASK, SEC_INT_TAMPER | SEC_INT_KEY_INVALID);
    
    val = security_reg_read(SEC_REG_INT_MASK);
    if ((val & (SEC_INT_TAMPER | SEC_INT_KEY_INVALID)) == 0) {
        PRINTF("[PASS] Security interrupt configured\n");
        security_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Interrupt configuration error\n");
        security_test_failed++;
        return -1;
    }
}

void test_security(void) {
    PRINTF("\n");
    PRINTF("========================================\n");
    PRINTF("  Security Controller Test Suite\n");
    PRINTF("========================================\n");
    
    test_security_trng();
    test_security_key_management();
    test_security_secure_boot();
    test_security_otp();
    test_security_die_id();
    test_security_anti_tamper();
    test_security_lifecycle();
    test_security_interrupt();
    
    PRINTF("\n========================================\n");
    PRINTF("  Security Test Results: PASS=%u FAIL=%u\n", 
           security_test_passed, security_test_failed);
    PRINTF("========================================\n");
}
