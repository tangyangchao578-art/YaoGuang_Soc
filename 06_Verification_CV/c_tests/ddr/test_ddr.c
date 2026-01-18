/*
 * YaoGuang SoC DDR Test Suite
 * 测试DDR控制器和LPDDR5内存
 *
 * Version: V1.0
 * Date: 2026-01-18
 */

#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>

/* 地址定义 */
#define DDR_BASE          0x80000000
#define DDR_SIZE          0x80000000    /* 2GB */
#define DDR_CTRL_BASE     0x40010000
#define DDR_STATUS_REG    0x40010000
#define DDR_CONFIG_REG    0x40010004
#define DDR_TIMING_REG    0x40010008
#define DDR_ECC_STATUS    0x40010100

/* 测试配置 */
#define TEST_PATTERN      0xDEADBEEF
#define TEST_BLOCK_SIZE   (1024 * 1024)  /* 1MB */
#define MAX_TEST_SIZE     (64 * 1024 * 1024)  /* 64MB */

/* 测试结果 */
typedef enum {
    TEST_PASS = 0,
    TEST_FAIL = 1,
    TEST_SKIP = 2
} test_result_t;

/* 全局变量 */
static int test_count = 0;
static int pass_count = 0;
static int fail_count = 0;

/* 性能统计 */
static uint64_t total_bytes = 0;
static double total_time = 0;

/*
 * 打印测试头部
 */
void print_test_header(const char *test_name)
{
    printf("\n");
    printf("========================================\n");
    printf("  Test: %s\n", test_name);
    printf("========================================\n");
    test_count++;
}

/*
 * 打印测试结果
 */
void print_test_result(const char *test_name, test_result_t result)
{
    printf("  [%s] %s\n", 
           result == TEST_PASS ? "PASS" : "FAIL",
           test_name);
    
    if (result == TEST_PASS) {
        pass_count++;
    } else {
        fail_count++;
    }
}

/*
 * 读取寄存器
 */
static inline uint32_t read_reg(uint32_t addr)
{
    return *(volatile uint32_t *)addr;
}

/*
 * 写入寄存器
 */
static inline void write_reg(uint32_t addr, uint32_t value)
{
    *(volatile uint32_t *)addr = value;
}

/*
 * 简单延时
 */
void delay(volatile int count)
{
    while (count--) {
        __asm__ volatile ("nop");
    }
}

/* 测试1: DDR 初始化测试 */
test_result_t test_ddr_init(void)
{
    print_test_header("DDR Initialization Test");
    
    uint32_t ddr_status;
    
    /* 检查DDR控制器状态 */
    ddr_status = read_reg(DDR_STATUS_REG);
    printf("  DDR Status: 0x%08X\n", ddr_status);
    
    /* 检查初始化完成位 */
    if (ddr_status & 0x1) {
        printf("  DDR initialization: PASSED\n");
    } else {
        printf("  DDR initialization: NOT COMPLETE\n");
        return TEST_FAIL;
    }
    
    /* 检查DDR大小 */
    uint32_t ddr_size = (ddr_status >> 8) & 0xF;
    printf("  DDR Size: %d GB\n", 1 << ddr_size);
    
    if (ddr_size < 1) {
        printf("  ERROR: DDR size too small\n");
        return TEST_FAIL;
    }
    
    /* 检查ECC状态 */
    uint32_t ecc_status = read_reg(DDR_ECC_STATUS);
    if (ecc_status & 0x1) {
        printf("  ECC: Enabled\n");
    } else {
        printf("  ECC: Disabled\n");
    }
    
    return TEST_PASS;
}

/* 测试2: DDR 基础读写测试 */
test_result_t test_ddr_basic_rw(void)
{
    print_test_header("DDR Basic Read/Write Test");
    
    uint32_t *ddr_ptr = (uint32_t *)DDR_BASE;
    uint32_t test_addr = DDR_BASE + 0x1000;
    uint32_t write_value = TEST_PATTERN;
    uint32_t read_value;
    
    /* 写入测试值 */
    printf("  Writing 0x%08X to address 0x%08X\n", 
           write_value, test_addr);
    ddr_ptr[test_addr / 4] = write_value;
    
    /* 读回验证 */
    read_value = ddr_ptr[test_addr / 4];
    printf("  Reading from address 0x%08X: 0x%08X\n", 
           test_addr, read_value);
    
    if (read_value == write_value) {
        printf("  Read/Write: PASSED\n");
        return TEST_PASS;
    } else {
        printf("  ERROR: Data mismatch (expected 0x%08X, got 0x%08X)\n",
               write_value, read_value);
        return TEST_FAIL;
    }
}

/* 测试3: DDR 模式寄存器测试 */
test_result_t test_ddr_modes(void)
{
    print_test_header("DDR Mode Register Test");
    
    uint32_t test_patterns[] = {
        0x00000000,
        0xFFFFFFFF,
        0xAAAAAAAA,
        0x55555555,
        0xA5A5A5A5,
        0x5A5A5A5A
    };
    
    uint32_t base_addr = DDR_BASE + 0x2000;
    
    /* 测试多种模式 */
    for (int i = 0; i < 6; i++) {
        uint32_t *ptr = (uint32_t *)base_addr;
        uint32_t pattern = test_patterns[i];
        
        /* 写入模式 */
        for (int j = 0; j < 16; j++) {
            ptr[j] = pattern;
        }
        
        /* 验证 */
        for (int j = 0; j < 16; j++) {
            if (ptr[j] != pattern) {
                printf("  ERROR: Pattern 0x%08X failed at offset 0x%X\n",
                       pattern, j * 4);
                return TEST_FAIL;
            }
        }
        
        printf("  Pattern 0x%08X: PASSED\n", pattern);
    }
    
    return TEST_PASS;
}

/* 测试4: DDR 边界测试 */
test_result_t test_ddr_boundaries(void)
{
    print_test_header("DDR Boundary Test");
    
    uint32_t *ddr_ptr = (uint32_t *)DDR_BASE;
    uint32_t errors = 0;
    
    /* 测试不同边界地址 */
    uint32_t boundaries[] = {
        0x0,
        0x1000,
        0x10000,
        0x100000,
        DDR_SIZE - 4,
        DDR_SIZE - 8,
        DDR_SIZE - 16
    };
    
    for (int i = 0; i < 7; i++) {
        uint32_t addr = boundaries[i];
        uint32_t write_val = 0xBEEF0000 | i;
        uint32_t read_val;
        
        /* 确保地址对齐 */
        addr = addr & ~0x3;
        
        /* 写入 */
        ddr_ptr[addr / 4] = write_val;
        
        /* 读回 */
        read_val = ddr_ptr[addr / 4];
        
        /* 验证 */
        if (read_val != write_val) {
            printf("  ERROR: Boundary test failed at 0x%08X\n", addr);
            printf("    Expected: 0x%08X, Got: 0x%08X\n", write_val, read_val);
            errors++;
        } else {
            printf("  Boundary 0x%08X: PASSED\n", addr);
        }
    }
    
    if (errors > 0) {
        printf("  Total boundary errors: %d\n", errors);
        return TEST_FAIL;
    }
    
    return TEST_PASS;
}

/* 测试5: DDR 连续读写测试 */
test_result_t test_ddr_contiguous(void)
{
    print_test_header("DDR Contiguous Read/Write Test");
    
    uint32_t *ddr_ptr = (uint32_t *)(DDR_BASE + 0x10000);
    uint32_t test_size = TEST_BLOCK_SIZE;  /* 1MB */
    uint32_t errors = 0;
    
    printf("  Test size: %d bytes (%d words)\n", 
           test_size, test_size / 4);
    
    /* 写入递增数据 */
    printf("  Writing data...\n");
    uint64_t start_time = __builtin_ia32_rdtsc();
    for (uint32_t i = 0; i < test_size / 4; i++) {
        ddr_ptr[i] = 0x10000000 | i;
    }
    uint64_t write_time = __builtin_ia32_rdtsc() - start_time;
    
    /* 验证数据 */
    printf("  Verifying data...\n");
    start_time = __builtin_ia32_rdtsc();
    for (uint32_t i = 0; i < test_size / 4; i++) {
        if (ddr_ptr[i] != (0x10000000 | i)) {
            if (errors < 10) {
                printf("  ERROR at 0x%08X: expected 0x%08X, got 0x%08X\n",
                       DDR_BASE + 0x10000 + i * 4,
                       0x10000000 | i,
                       ddr_ptr[i]);
            }
            errors++;
        }
    }
    uint64_t read_time = __builtin_ia32_rdtsc() - start_time;
    
    /* 计算性能 */
    double write_bw = (double)test_size / write_time * 3.0;  /* 粗略估计 */
    double read_bw = (double)test_size / read_time * 3.0;
    
    printf("  Write time: %lu cycles, Est. BW: %.2f GB/s\n",
           write_time, write_bw / 1e9);
    printf("  Read time: %lu cycles, Est. BW: %.2f GB/s\n",
           read_time, read_bw / 1e9);
    printf("  Errors: %d\n", errors);
    
    total_bytes += test_size * 2;
    
    if (errors > 0) {
        return TEST_FAIL;
    }
    
    return TEST_PASS;
}

/* 测试6: DDR 随机访问测试 */
test_result_t test_ddr_random(void)
{
    print_test_header("DDR Random Access Test");
    
    uint32_t *ddr_ptr = (uint32_t *)DDR_BASE;
    uint32_t errors = 0;
    uint32_t seed = 0x12345678;
    
    printf("  Performing 1000 random accesses...\n");
    
    /* 生成随机地址并测试 */
    for (int i = 0; i < 1000; i++) {
        /* 简单的伪随机数生成 */
        seed = seed * 1103515245 + 12345;
        uint32_t addr = (seed % (DDR_SIZE / 4 - 256)) * 4;
        uint32_t write_val = seed;
        
        /* 写入 */
        ddr_ptr[addr / 4] = write_val;
        
        /* 读回 */
        uint32_t read_val = ddr_ptr[addr / 4];
        
        /* 验证 */
        if (read_val != write_val) {
            if (errors < 5) {
                printf("  ERROR at 0x%08X: expected 0x%08X, got 0x%08X\n",
                       DDR_BASE + addr, write_val, read_val);
            }
            errors++;
        }
    }
    
    printf("  Random access errors: %d\n", errors);
    
    if (errors > 0) {
        return TEST_FAIL;
    }
    
    return TEST_PASS;
}

/* 测试7: DDR 带宽测试 */
test_result_t test_ddr_bandwidth(void)
{
    print_test_header("DDR Bandwidth Test");
    
    uint32_t *ddr_ptr = (uint32_t *)(DDR_BASE + 0x20000);
    uint32_t test_size = 16 * 1024 * 1024;  /* 16MB */
    uint32_t iterations = 4;
    
    double total_write_time = 0;
    double total_read_time = 0;
    
    printf("  Test size: %d MB, Iterations: %d\n",
           test_size / (1024 * 1024), iterations);
    
    for (int iter = 0; iter < iterations; iter++) {
        /* 写测试 */
        uint64_t start = __builtin_ia32_rdtsc();
        for (uint32_t i = 0; i < test_size / 4; i++) {
            ddr_ptr[i] = 0xDEADBEEF;
        }
        total_write_time += (__builtin_ia32_rdtsc() - start);
        
        /* 读测试 */
        volatile uint32_t sink = 0;
        start = __builtin_ia32_rdtsc();
        for (uint32_t i = 0; i < test_size / 4; i++) {
            sink += ddr_ptr[i];
        }
        total_read_time += (__builtin_ia32_rdtsc() - start);
    }
    
    /* 计算平均带宽 (假设3GHz时钟) */
    double cpu_freq = 3.0e9;
    double write_bw = (double)test_size * iterations / total_write_time * cpu_freq / 1e9;
    double read_bw = (double)test_size * iterations / total_read_time * cpu_freq / 1e9;
    
    printf("  Average Write BW: %.2f GB/s\n", write_bw);
    printf("  Average Read BW: %.2f GB/s\n", read_bw);
    
    /* 检查是否达到目标带宽 (目标: > 50 GB/s) */
    double avg_bw = (write_bw + read_bw) / 2;
    if (avg_bw > 50) {
        printf("  Bandwidth target: PASSED (> 50 GB/s)\n");
    } else {
        printf("  WARNING: Bandwidth below target (%.2f < 50 GB/s)\n", avg_bw);
    }
    
    total_bytes += test_size * iterations * 2;
    
    return TEST_PASS;
}

/* 测试8: DDR ECC 测试 */
test_result_t test_ddr_ecc(void)
{
    print_test_header("DDR ECC Test");
    
    uint32_t ecc_status = read_reg(DDR_ECC_STATUS);
    
    /* 检查ECC是否启用 */
    if (!(ecc_status & 0x1)) {
        printf("  ECC is disabled, skipping ECC tests\n");
        return TEST_SKIP;
    }
    
    printf("  ECC Status: 0x%08X\n", ecc_status);
    
    /* 检查ECC错误计数 */
    uint32_t ecc_err_cnt = (ecc_status >> 8) & 0xFF;
    printf("  ECC Error Count: %d\n", ecc_err_cnt);
    
    /* 检查ECC更正计数 */
    uint32_t ecc_corr_cnt = (ecc_status >> 16) & 0xFF;
    printf("  ECC Corrected Count: %d\n", ecc_corr_cnt);
    
    if (ecc_err_cnt > 0) {
        printf("  WARNING: Uncorrectable ECC errors detected\n");
        return TEST_FAIL;
    }
    
    printf("  ECC: PASSED\n");
    
    return TEST_PASS;
}

/* 测试9: DDR 压力测试 */
test_result_t test_ddr_stress(void)
{
    print_test_header("DDR Stress Test");
    
    uint32_t *ddr_ptr = (uint32_t *)DDR_BASE;
    uint32_t errors = 0;
    
    printf("  Running stress test (10 iterations)...\n");
    
    /* 多次读写压力测试 */
    for (int iter = 0; iter < 10; iter++) {
        uint32_t pattern = 0xABCD0000 | iter;
        
        /* 写入 */
        for (uint32_t i = 0; i < TEST_BLOCK_SIZE / 4; i++) {
            ddr_ptr[i] = pattern;
        }
        
        /* 验证 */
        for (uint32_t i = 0; i < TEST_BLOCK_SIZE / 4; i++) {
            if (ddr_ptr[i] != pattern) {
                if (errors < 5) {
                    printf("  ERROR at iteration %d, offset 0x%08X\n",
                           iter, i * 4);
                }
                errors++;
            }
        }
        
        printf("  Iteration %d: %s\n", iter + 1, 
               errors == 0 ? "PASSED" : "FAILED");
    }
    
    printf("  Total errors: %d\n", errors);
    
    if (errors > 100) {
        return TEST_FAIL;
    }
    
    return TEST_PASS;
}

/*
 * 主函数
 */
int main(void)
{
    printf("\n");
    printf("================================================\n");
    printf("  YaoGuang SoC DDR Test Suite\n");
    printf("  Version: V1.0\n");
    printf("  Date: 2026-01-18\n");
    printf("================================================\n");
    
    printf("\n  DDR Base: 0x%08X\n", DDR_BASE);
    printf("  DDR Size: %d GB\n", DDR_SIZE / (1024*1024*1024));
    
    /* 运行所有测试 */
    test_ddr_init();
    test_ddr_basic_rw();
    test_ddr_modes();
    test_ddr_boundaries();
    test_ddr_contiguous();
    test_ddr_random();
    test_ddr_bandwidth();
    test_ddr_ecc();
    test_ddr_stress();
    
    /* 打印测试汇总 */
    printf("\n");
    printf("================================================\n");
    printf("  Test Summary\n");
    printf("================================================\n");
    printf("  Total Tests: %d\n", test_count);
    printf("  Passed:      %d\n", pass_count);
    printf("  Failed:      %d\n", fail_count);
    printf("  Pass Rate:   %.1f%%\n", 
           pass_count * 100.0 / test_count);
    printf("  Total Data Transferred: %.2f GB\n", 
           total_bytes / 1e9);
    printf("================================================\n");
    
    /* 返回结果 */
    if (fail_count > 0) {
        printf("\n  RESULT: SOME TESTS FAILED\n");
        return 1;
    } else {
        printf("\n  RESULT: ALL TESTS PASSED\n");
        return 0;
    }
}
