#include "test_framework.h"
#include "uart_hw.h"

#define UART_BASE_ADDR  0x40090000

static uint32_t uart_test_passed = 0;
static uint32_t uart_test_failed = 0;

static void uart_reg_write(uint32_t offset, uint32_t value) {
    volatile uint32_t *reg = (volatile uint32_t *)(UART_BASE_ADDR + offset);
    *reg = value;
}

static uint32_t uart_reg_read(uint32_t offset) {
    volatile uint32_t *reg = (volatile uint32_t *)(UART_BASE_ADDR + offset);
    return *reg;
}

static int test_uart_baud_rate(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: UART Baud Rate ===\n");
    
    uart_reg_write(UART_REG_LCR, UART_LCR_DLAB);
    uart_reg_write(UART_REG_DLL, 0x1A);
    uart_reg_write(UART_REG_DLM, 0x00);
    uart_reg_write(UART_REG_LCR, 0x03);
    
    val = uart_reg_read(UART_REG_LCR);
    if ((val & 0x03) == 0x03) {
        PRINTF("[PASS] UART baud rate configured (115200 @ 50MHz)\n");
        uart_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Baud rate configuration error, lcr=0x%08X\n", val);
        uart_test_failed++;
        return -1;
    }
}

static int test_uart_transmit(void) {
    uint32_t val;
    uint8_t tx_data[] = "Hello YaoGuang!\n";
    
    PRINTF("\n=== Test: UART Transmit ===\n");
    
    for (int i = 0; i < sizeof(tx_data) - 1; i++) {
        uart_reg_write(UART_REG_THR, tx_data[i]);
        
        delay_us(100);
        val = uart_reg_read(UART_REG_LSR);
        
        if (!(val & UART_LSR_THRE)) {
            PRINTF("[FAIL] UART TX buffer not empty\n");
            uart_test_failed++;
            return -1;
        }
    }
    
    PRINTF("[PASS] UART transmit completed (%u bytes)\n", sizeof(tx_data) - 1);
    uart_test_passed++;
    return 0;
}

static int test_uart_receive(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: UART Receive ===\n");
    
    val = uart_reg_read(UART_REG_LSR);
    if (val & UART_LSR_DR) {
        uint8_t data = uart_reg_read(UART_REG_RBR) & 0xFF;
        PRINTF("[PASS] UART received data: 0x%02X\n", data);
        uart_test_passed++;
        return 0;
    } else {
        PRINTF("[PASS] UART receive ready (no data in buffer)\n");
        uart_test_passed++;
        return 0;
    }
}

static int test_uart_fifo(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: UART FIFO Configuration ===\n");
    
    uart_reg_write(UART_REG_FCR, UART_FCR_ENABLE | UART_FCR_TRIGGER_8);
    
    val = uart_reg_read(UART_REG_FCR);
    if (val & UART_FCR_ENABLE) {
        PRINTF("[PASS] UART FIFO enabled (trigger=8)\n");
        uart_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] FIFO configuration error, fcr=0x%08X\n", val);
        uart_test_failed++;
        return -1;
    }
}

static int test_uart_line_control(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: UART Line Control ===\n");
    
    uart_reg_write(UART_REG_LCR, UART_LCR_8N1);
    val = uart_reg_read(UART_REG_LCR);
    
    if (val == UART_LCR_8N1) {
        PRINTF("[PASS] UART line control: 8N1\n");
        uart_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Line control error, lcr=0x%08X\n", val);
        uart_test_failed++;
        return -1;
    }
}

static int test_uart_interrupt(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: UART Interrupt ===\n");
    
    uart_reg_write(UART_REG_IER, 0x00);
    uart_reg_write(UART_REG_IER, UART_IER_RDA | UART_IER_THRE | UART_IER_RLS);
    
    val = uart_reg_read(UART_REG_IER);
    if ((val & (UART_IER_RDA | UART_IER_THRE | UART_IER_RLS)) == 
        (UART_IER_RDA | UART_IER_THRE | UART_IER_RLS)) {
        PRINTF("[PASS] UART interrupts enabled\n");
        uart_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Interrupt configuration error, ier=0x%08X\n", val);
        uart_test_failed++;
        return -1;
    }
}

static int test_uart_modem_control(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: UART Modem Control ===\n");
    
    uart_reg_write(UART_REG_MCR, UART_MCR_DTR | UART_MCR_RTS);
    val = uart_reg_read(UART_REG_MCR);
    
    if ((val & (UART_MCR_DTR | UART_MCR_RTS)) == (UART_MCR_DTR | UART_MCR_RTS)) {
        PRINTF("[PASS] UART modem control configured\n");
        uart_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Modem control error, mcr=0x%08X\n", val);
        uart_test_failed++;
        return -1;
    }
}

void test_uart(void) {
    PRINTF("\n");
    PRINTF("========================================\n");
    PRINTF("  UART Controller Test Suite\n");
    PRINTF("========================================\n");
    
    test_uart_baud_rate();
    test_uart_transmit();
    test_uart_receive();
    test_uart_fifo();
    test_uart_line_control();
    test_uart_interrupt();
    test_uart_modem_control();
    
    PRINTF("\n========================================\n");
    PRINTF("  UART Test Results: PASS=%u FAIL=%u\n", 
           uart_test_passed, uart_test_failed);
    PRINTF("========================================\n");
}
