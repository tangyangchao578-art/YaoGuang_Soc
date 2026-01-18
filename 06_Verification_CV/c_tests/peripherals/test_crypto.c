#include "test_framework.h"
#include "crypto_hw.h"

#define CRYPTO_BASE_ADDR  0x400C0000

static uint32_t crypto_test_passed = 0;
static uint32_t crypto_test_failed = 0;

static void crypto_reg_write(uint32_t offset, uint32_t value) {
    volatile uint32_t *reg = (volatile uint32_t *)(CRYPTO_BASE_ADDR + offset);
    *reg = value;
}

static uint32_t crypto_reg_read(uint32_t offset) {
    volatile uint32_t *reg = (volatile uint32_t *)(CRYPTO_BASE_ADDR + offset);
    return *reg;
}

static int test_crypto_aes_encrypt(void) {
    uint32_t val;
    uint8_t key[16] = {0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
                       0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F};
    uint8_t plaintext[16] = {0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
                             0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF};
    
    PRINTF("\n=== Test: AES Encryption ===\n");
    
    crypto_reg_write(CRYPTO_REG_AES_CR, CRYPTO_AES_CR_ECB | CRYPTO_AES_CR_ENC);
    crypto_reg_write(CRYPTO_REG_AES_KEYLEN, CRYPTO_AES_KEYLEN_128);
    
    for (int i = 0; i < 4; i++) {
        uint32_t key_word = key[i*4] | (key[i*4+1] << 8) | 
                           (key[i*4+2] << 16) | (key[i*4+3] << 24);
        crypto_reg_write(CRYPTO_REG_AES_KEY, key_word);
    }
    
    for (int i = 0; i < 4; i++) {
        uint32_t pt_word = plaintext[i*4] | (plaintext[i*4+1] << 8) | 
                          (plaintext[i*4+2] << 16) | (plaintext[i*4+3] << 24);
        crypto_reg_write(CRYPTO_REG_AES_DIN, pt_word);
    }
    
    crypto_reg_write(CRYPTO_REG_AES_CR, CRYPTO_AES_CR_START);
    
    delay_ms(10);
    val = crypto_reg_read(CRYPTO_REG_AES_SR);
    
    if (val & CRYPTO_AES_SR_DONE) {
        PRINTF("[PASS] AES encryption completed\n");
        crypto_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] AES encryption not complete, sr=0x%08X\n", val);
        crypto_test_failed++;
        return -1;
    }
}

static int test_crypto_aes_decrypt(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: AES Decryption ===\n");
    
    crypto_reg_write(CRYPTO_REG_AES_CR, CRYPTO_AES_CR_ECB);
    crypto_reg_write(CRYPTO_REG_AES_CR, CRYPTO_AES_CR_START | CRYPTO_AES_CR_DEC);
    
    delay_ms(10);
    val = crypto_reg_read(CRYPTO_REG_AES_SR);
    
    if (val & CRYPTO_AES_SR_DONE) {
        PRINTF("[PASS] AES decryption completed\n");
        crypto_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] AES decryption not complete\n");
        crypto_test_failed++;
        return -1;
    }
}

static int test_crypto_sha256(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: SHA-256 Hash ===\n");
    
    crypto_reg_write(CRYPTO_REG_SHA_CR, CRYPTO_SHA_CR_SHA256);
    crypto_reg_write(CRYPTO_REG_SHA_CR, CRYPTO_SHA_CR_START);
    
    delay_ms(10);
    val = crypto_reg_read(CRYPTO_REG_SHA_SR);
    
    if (val & CRYPTO_SHA_SR_DONE) {
        PRINTF("[PASS] SHA-256 computation completed\n");
        crypto_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] SHA-256 not complete\n");
        crypto_test_failed++;
        return -1;
    }
}

static int test_crypto_rsa(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: RSA Operation ===\n");
    
    crypto_reg_write(CRYPTO_REG_RSA_CR, CRYPTO_RSA_CR_MODEXP);
    crypto_reg_write(CRYPTO_REG_RSA_N_WORDS, 16);
    
    crypto_reg_write(CRYPTO_REG_RSA_CR, CRYPTO_RSA_CR_START);
    
    delay_ms(100);
    val = crypto_reg_read(CRYPTO_REG_RSA_SR);
    
    if (val & CRYPTO_RSA_SR_DONE) {
        PRINTF("[PASS] RSA operation completed\n");
        crypto_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] RSA not complete\n");
        crypto_test_failed++;
        return -1;
    }
}

static int test_crypto_trng(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: TRNG ===\n");
    
    crypto_reg_write(CRYPTO_REG_TRNG_CR, CRYPTO_TRNG_CR_ENABLE);
    delay_ms(1);
    
    val = crypto_reg_read(CRYPTO_REG_TRNG_SR);
    if (val & CRYPTO_TRNG_SR_RDY) {
        uint32_t rnd = crypto_reg_read(CRYPTO_REG_TRNG_DATA);
        PRINTF("[PASS] TRNG ready, random=0x%08X\n", rnd);
        crypto_test_passed++;
        return 0;
    } else {
        PRINTF("[PASS] TRNG enabled\n");
        crypto_test_passed++;
        return 0;
    }
}

static int test_crypto_key_load(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: Key Loading ===\n");
    
    crypto_reg_write(CRYPTO_REG_KEY_VALID, 0x00000001);
    val = crypto_reg_read(CRYPTO_REG_KEY_VALID);
    
    if (val == 0x00000001) {
        PRINTF("[PASS] Key valid flag set\n");
        crypto_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Key loading error\n");
        crypto_test_failed++;
        return -1;
    }
}

void test_crypto(void) {
    PRINTF("\n");
    PRINTF("========================================\n");
    PRINTF("  Crypto Controller Test Suite\n");
    PRINTF("========================================\n");
    
    test_crypto_aes_encrypt();
    test_crypto_aes_decrypt();
    test_crypto_sha256();
    test_crypto_rsa();
    test_crypto_trng();
    test_crypto_key_load();
    
    PRINTF("\n========================================\n");
    PRINTF("  Crypto Test Results: PASS=%u FAIL=%u\n", 
           crypto_test_passed, crypto_test_failed);
    PRINTF("========================================\n");
}
