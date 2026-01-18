#ifndef TEST_FRAMEWORK_H
#define TEST_FRAMEWORK_H

#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>

#define PRINTF(...)     printf(__VA_ARGS__)
#define delay_ms(ms)    platform_delay_ms(ms)
#define delay_us(us)    platform_delay_us(us)

#define TEST_PASSED     0
#define TEST_FAILED     -1

#define MAX_TEST_NAME   64

typedef struct {
    const char *name;
    int (*test_func)(void);
    uint32_t passed;
    uint32_t failed;
} test_suite_t;

typedef struct {
    uint32_t pass_count;
    uint32_t fail_count;
    uint32_t total_count;
} test_result_t;

void platform_delay_ms(uint32_t ms);
void platform_delay_us(uint32_t us);

void test_framework_init(void);
int test_framework_run_suite(test_suite_t *suite);
void test_framework_print_summary(test_result_t *result);

#define TEST_SUITE(name) \
    test_suite_t name##_suite = { \
        .name = #name, \
        .test_func = test_##name, \
        .passed = 0, \
        .failed = 0 \
    }

#define RUN_TEST(func) \
    do { \
        PRINTF("\n[RUN ] %s\n", #func); \
        if (func() == TEST_PASSED) { \
            PRINTF("[OK  ] %s passed\n", #func); \
        } else { \
            PRINTF("[ERR ] %s failed\n", #func); \
        } \
    } while(0)

#endif
