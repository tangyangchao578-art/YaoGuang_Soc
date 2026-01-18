#include "test_framework.h"
#include "pcie_hw.h"
#include "ethernet_hw.h"
#include "usb_hw.h"
#include "can_hw.h"
#include "gpio_hw.h"
#include "i2c_hw.h"
#include "spi_hw.h"
#include "uart_hw.h"
#include "display_hw.h"
#include "audio_hw.h"
#include "crypto_hw.h"
#include "security_hw.h"

void platform_delay_ms(uint32_t ms) {
    volatile uint32_t count = ms * 10000;
    while (count--) { }
}

void platform_delay_us(uint32_t us) {
    volatile uint32_t count = us * 10;
    while (count--) { }
}

void test_framework_init(void) {
    PRINTF("\n");
    PRINTF("****************************************\n");
    PRINTF("  YaoGuang SoC Peripheral Test Suite\n");
    PRINTF("  CV Verification - System Level\n");
    PRINTF("****************************************\n\n");
}

void test_framework_print_summary(test_result_t *result) {
    PRINTF("\n");
    PRINTF("========================================\n");
    PRINTF("  Final Test Summary\n");
    PRINTF("========================================\n");
    PRINTF("  Total Tests: %u\n", result->total_count);
    PRINTF("  Passed:      %u\n", result->pass_count);
    PRINTF("  Failed:      %u\n", result->fail_count);
    PRINTF("  Pass Rate:   %u%%\n", 
           result->total_count > 0 ? (result->pass_count * 100 / result->total_count) : 0);
    PRINTF("========================================\n\n");
}

int main(void) {
    test_result_t result = {0, 0, 0};
    
    test_framework_init();
    
    PRINTF("Running all peripheral tests...\n\n");
    
    test_pcie();
    result.total_count += 12;
    
    test_ethernet();
    result.total_count += 5;
    
    test_usb();
    result.total_count += 5;
    
    test_can();
    result.total_count += 5;
    
    test_gpio();
    result.total_count += 6;
    
    test_i2c();
    result.total_count += 6;
    
    test_spi();
    result.total_count += 6;
    
    test_uart();
    result.total_count += 7;
    
    test_display();
    result.total_count += 6;
    
    test_audio();
    result.total_count += 8;
    
    test_crypto();
    result.total_count += 6;
    
    test_security();
    result.total_count += 8;
    
    test_framework_print_summary(&result);
    
    return result.fail_count > 0 ? 1 : 0;
}
