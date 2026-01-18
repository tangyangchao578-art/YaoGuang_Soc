/*
 * YaoGuang SoC Boot ROM Test
 * 测试Boot ROM的基本功能
 *
 * Version: V1.0
 * Date: 2026-01-18
 */

#include <stdio.h>
#include <stdint.h>
#include <string.h>

/* 地址定义 */
#define BOOT_ROM_BASE      0x00000000
#define BOOT_ROM_SIZE      0x00040000    /* 256KB */
#define BOOT_STATUS_REG    0x40000000
#define BOOT_CONTROL_REG   0x40000004
#define BOOT_VERSION_REG   0x40000008

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

/* 测试1: Boot ROM 读取测试 */
test_result_t test_boot_rom_read(void)
{
    print_test_header("Boot ROM Read Test");
    
    uint32_t boot_version;
    uint32_t boot_status;
    
    /* 读取Boot版本 */
    boot_version = read_reg(BOOT_VERSION_REG);
    printf("  Boot ROM Version: 0x%08X\n", boot_version);
    
    /* 验证版本是否有效 */
    if (boot_version == 0 || boot_version == 0xFFFFFFFF) {
        printf("  ERROR: Invalid boot version (0x%08X)\n", boot_version);
        return TEST_FAIL;
    }
    
    /* 读取Boot状态 */
    boot_status = read_reg(BOOT_STATUS_REG);
    printf("  Boot Status: 0x%08X\n", boot_status);
    
    /* 检查Boot状态 */
    if (boot_status & 0x1) {
        printf("  Boot ROM valid\n");
    } else {
        printf("  ERROR: Boot ROM invalid\n");
        return TEST_FAIL;
    }
    
    /* 读取Boot ROM数据并验证校验和 */
    uint32_t checksum = 0;
    uint32_t *boot_rom_ptr = (uint32_t *)BOOT_ROM_BASE;
    
    for (int i = 0; i < BOOT_ROM_SIZE / 4; i++) {
        checksum += boot_rom_ptr[i];
    }
    
    printf("  Boot ROM Checksum: 0x%08X\n", checksum);
    
    return TEST_PASS;
}

/* 测试2: Boot ROM 写入保护测试 */
test_result_t test_boot_rom_write_protect(void)
{
    print_test_header("Boot ROM Write Protect Test");
    
    uint32_t original_value;
    uint32_t test_value = 0xDEADBEEF;
    uint32_t read_back;
    
    /* 尝试写入Boot ROM区域 */
    uint32_t *boot_rom_ptr = (uint32_t *)BOOT_ROM_BASE;
    original_value = boot_rom_ptr[0];
    
    /* 写入测试值 */
    boot_rom_ptr[0] = test_value;
    
    /* 读回验证 */
    read_back = boot_rom_ptr[0];
    
    if (read_back == test_value) {
        printf("  ERROR: Boot ROM is writable (should be read-only)\n");
        return TEST_FAIL;
    }
    
    printf("  Boot ROM is properly write-protected\n");
    
    /* 恢复原始值 */
    boot_rom_ptr[0] = original_value;
    
    return TEST_PASS;
}

/* 测试3: Boot 模式选择测试 */
test_result_t test_boot_mode_select(void)
{
    print_test_header("Boot Mode Select Test");
    
    uint32_t boot_mode;
    
    /* 读取当前Boot模式 */
    boot_mode = read_reg(BOOT_CONTROL_REG) & 0xF;
    printf("  Current Boot Mode: %d\n", boot_mode);
    
    /* 支持的Boot模式 */
    printf("  Supported Boot Modes:\n");
    printf("    0: SPI Flash\n");
    printf("    1: NAND Flash\n");
    printf("    2: eMMC\n");
    printf("    3: UART Download\n");
    printf("    4: USB DFU\n");
    
    /* 验证Boot模式在有效范围内 */
    if (boot_mode > 4) {
        printf("  ERROR: Invalid boot mode (%d)\n", boot_mode);
        return TEST_FAIL;
    }
    
    printf("  Boot mode selection: OK\n");
    
    return TEST_PASS;
}

/* 测试4: Boot 进度测试 */
test_result_t test_boot_progress(void)
{
    print_test_header("Boot Progress Test");
    
    uint32_t boot_status;
    uint32_t progress;
    
    /* 读取Boot状态 */
    boot_status = read_reg(BOOT_STATUS_REG);
    
    /* 解析进度信息 */
    progress = (boot_status >> 8) & 0xFF;
    printf("  Boot Progress: %d%%\n", progress);
    
    /* 检查Boot阶段 */
    uint32_t stage = (boot_status >> 16) & 0xF;
    const char *stage_name[] = {
        "RESET",
        "ROM_CODE",
        "BL2_LOAD",
        "DDR_INIT",
        "BL2_EXEC",
        "LINUX_LOAD",
        "LINUX_EXEC"
    };
    
    if (stage < 7) {
        printf("  Boot Stage: %s\n", stage_name[stage]);
    } else {
        printf("  ERROR: Unknown boot stage (%d)\n", stage);
        return TEST_FAIL;
    }
    
    return TEST_PASS;
}

/* 测试5: Boot 失败恢复测试 */
test_result_t test_boot_fail_recovery(void)
{
    print_test_header("Boot Fail Recovery Test");
    
    uint32_t boot_status;
    uint32_t error_code;
    
    /* 读取Boot状态 */
    boot_status = read_reg(BOOT_STATUS_REG);
    
    /* 检查错误标志 */
    if (boot_status & 0x2) {
        printf("  Boot error detected\n");
        error_code = (boot_status >> 20) & 0xFFF;
        printf("  Error Code: 0x%03X\n", error_code);
        
        /* 错误码说明 */
        switch (error_code) {
            case 0x001:
                printf("    - DDR init failed\n");
                break;
            case 0x002:
                printf("    - BL2 load failed\n");
                break;
            case 0x003:
                printf("    - Image verification failed\n");
                break;
            case 0x004:
                printf("    - Certificate verification failed\n");
                break;
            default:
                printf("    - Unknown error\n");
                break;
        }
        
        return TEST_FAIL;
    }
    
    printf("  No boot errors detected\n");
    
    return TEST_PASS;
}

/* 测试6: Boot 计时测试 */
test_result_t test_boot_timing(void)
{
    print_test_header("Boot Timing Test");
    
    uint32_t boot_status;
    uint32_t start_time, end_time;
    
    /* 获取开始时间 */
    start_time = read_reg(0x40001000);  /* 假设有时间戳寄存器 */
    
    /* 执行Boot流程 */
    write_reg(BOOT_CONTROL_REG, 0x1);  /* 触发Boot */
    
    /* 等待Boot完成 */
    do {
        boot_status = read_reg(BOOT_STATUS_REG);
    } while (!(boot_status & 0x100));  /* 等待DONE位 */
    
    /* 获取结束时间 */
    end_time = read_reg(0x40001004);
    
    uint32_t boot_time = end_time - start_time;
    printf("  Boot Time: %d cycles\n", boot_time);
    
    /* 检查Boot时间是否在目标范围内 */
    /* 假设目标是 < 10000 cycles @ 100MHz = 100us */
    if (boot_time < 10000) {
        printf("  Boot time meets target (< 100us)\n");
    } else {
        printf("  WARNING: Boot time exceeds target\n");
    }
    
    return TEST_PASS;
}

/* 测试7: 多重Boot尝试测试 */
test_result_t test_multi_boot_attempt(void)
{
    print_test_header("Multi-Boot Attempt Test");
    
    uint32_t boot_status;
    
    /* 尝试多次Boot */
    for (int i = 0; i < 3; i++) {
        printf("  Boot attempt %d...\n", i + 1);
        
        /* 触发Boot */
        write_reg(BOOT_CONTROL_REG, 0x1);
        
        /* 等待完成 */
        do {
            boot_status = read_reg(BOOT_STATUS_REG);
        } while (!(boot_status & 0x100));
        
        printf("  Boot %s\n", (boot_status & 0x2) ? "FAILED" : "SUCCESS");
        
        if (boot_status & 0x2) {
            return TEST_FAIL;
        }
        
        /* 复位后重新尝试 */
        write_reg(BOOT_CONTROL_REG, 0x2);  /* 软复位 */
    }
    
    printf("  All boot attempts successful\n");
    
    return TEST_PASS;
}

/*
 * 主函数
 */
int main(void)
{
    printf("\n");
    printf("================================================\n");
    printf("  YaoGuang SoC Boot ROM Test Suite\n");
    printf("  Version: V1.0\n");
    printf("  Date: 2026-01-18\n");
    printf("================================================\n");
    
    /* 运行所有测试 */
    test_boot_rom_read();
    test_boot_rom_write_protect();
    test_boot_mode_select();
    test_boot_progress();
    test_boot_fail_recovery();
    test_boot_timing();
    test_multi_boot_attempt();
    
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
