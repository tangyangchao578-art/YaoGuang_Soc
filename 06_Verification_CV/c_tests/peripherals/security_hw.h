#ifndef SECURITY_HW_H
#define SECURITY_HW_H

#include <stdint.h>

#define SECURITY_BASE_ADDR  0x400D0000

#define SEC_REG_TRNG_CR         0x0000
#define SEC_REG_TRNG_SR         0x0004
#define SEC_REG_TRNG_DATA       0x0008
#define SEC_REG_KEY_CR          0x0010
#define SEC_REG_KEY_INDEX       0x0014
#define SEC_REG_KEY_VALID       0x0018
#define SEC_REG_BOOT_CR         0x0020
#define SEC_REG_BOOT_MODE       0x0024
#define SEC_REG_OTP_CR          0x0030
#define SEC_REG_OTP_ADDR        0x0034
#define SEC_REG_OTP_DATA        0x0038
#define SEC_REG_DIE_ID_0        0x0040
#define SEC_REG_DIE_ID_1        0x0044
#define SEC_REG_DIE_ID_2        0x0048
#define SEC_REG_DIE_ID_3        0x004C
#define SEC_REG_TAMPER_CR       0x0050
#define SEC_REG_TAMPER_MASK     0x0054
#define SEC_REG_LIFECYCLE       0x0060
#define SEC_REG_INT_STATUS      0x0070
#define SEC_REG_INT_MASK        0x0074
#define SEC_REG_INT_CLEAR       0x0078

#define SEC_TRNG_CR_ENABLE      0x00000001
#define SEC_TRNG_CR_START       0x00000002
#define SEC_TRNG_SR_RDY         0x00000001
#define SEC_KEY_CR_WRITE        0x00000001
#define SEC_KEY_CR_READ         0x00000002
#define SEC_KEY_VALID           0x00000001
#define SEC_BOOT_CR_VERIFY      0x00000001
#define SEC_BOOT_MODE_SECURE    0x00000001
#define SEC_OTP_CR_READ         0x00000001
#define SEC_OTP_CR_WRITE        0x00000002
#define SEC_TAMPER_CR_ENABLE    0x00000001
#define SEC_TAMPER_VOLTAGE      0x00000001
#define SEC_TEMP_SENSOR         0x00000002
#define SEC_INT_TAMPER          0x00000001
#define SEC_INT_KEY_INVALID     0x00000002

void test_security(void);

#endif
