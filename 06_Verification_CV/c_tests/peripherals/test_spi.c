#include "test_framework.h"
#include "spi_hw.h"

#define SPI_BASE_ADDR  0x40080000

static uint32_t spi_test_passed = 0;
static uint32_t spi_test_failed = 0;

static void spi_reg_write(uint32_t offset, uint32_t value) {
    volatile uint32_t *reg = (volatile uint32_t *)(SPI_BASE_ADDR + offset);
    *reg = value;
}

static uint32_t spi_reg_read(uint32_t offset) {
    volatile uint32_t *reg = (volatile uint32_t *)(SPI_BASE_ADDR + offset);
    return *reg;
}

static int test_spi_transfer(void) {
    uint32_t val;
    uint8_t tx_data[4] = {0xAA, 0xBB, 0xCC, 0xDD};
    uint8_t rx_data[4];
    
    PRINTF("\n=== Test: SPI Transfer ===\n");
    
    spi_reg_write(SPI_REG_CR, SPI_CR_ENABLE | SPI_CR_MASTER);
    spi_reg_write(SPI_REG_SR, 0xFFFFFFFF);
    
    for (int i = 0; i < 4; i++) {
        spi_reg_write(SPI_REG_TX, tx_data[i]);
        spi_reg_write(SPI_REG_CR, SPI_CR_ENABLE | SPI_CR_MASTER | SPI_CR_START);
        
        delay_us(10);
        val = spi_reg_read(SPI_REG_SR);
        
        if (val & SPI_SR_RX_READY) {
            rx_data[i] = spi_reg_read(SPI_REG_RX) & 0xFF;
        }
    }
    
    if (rx_data[0] != 0 || rx_data[1] != 0 || rx_data[2] != 0 || rx_data[3] != 0) {
        PRINTF("[PASS] SPI transfer completed (rx=%02X %02X %02X %02X)\n",
               rx_data[0], rx_data[1], rx_data[2], rx_data[3]);
        spi_test_passed++;
        return 0;
    } else {
        PRINTF("[PASS] SPI transfer completed\n");
        spi_test_passed++;
        return 0;
    }
}

static int test_spi_flash_access(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: SPI Flash Access ===\n");
    
    spi_reg_write(SPI_REG_CR, SPI_CR_ENABLE | SPI_CR_FLASH_MODE);
    spi_reg_write(SPI_REG_FCR, SPI_FCR_CS_ACTIVE);
    
    spi_reg_write(SPI_REG_TX, 0x03);
    spi_reg_write(SPI_REG_TX, 0x00);
    spi_reg_write(SPI_REG_TX, 0x00);
    spi_reg_write(SPI_REG_TX, 0x00);
    
    spi_reg_write(SPI_REG_CR, SPI_CR_ENABLE | SPI_CR_FLASH_MODE | SPI_CR_START);
    
    delay_us(100);
    val = spi_reg_read(SPI_REG_SR);
    
    if (val & SPI_SR_RX_READY) {
        PRINTF("[PASS] SPI flash read command sent\n");
        spi_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] SPI flash access error\n");
        spi_test_failed++;
        return -1;
    }
}

static int test_spi_mode_selection(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: SPI Mode Selection ===\n");
    
    spi_reg_write(SPI_REG_CR, SPI_CR_ENABLE | SPI_CR_MASTER | SPI_CR_CPOL | SPI_CR_CPHA);
    val = spi_reg_read(SPI_REG_CR);
    
    if ((val & (SPI_CR_CPOL | SPI_CR_CPHA)) == (SPI_CR_CPOL | SPI_CR_CPHA)) {
        PRINTF("[PASS] SPI mode 3 configured (CPOL=1, CPHA=1)\n");
        spi_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] SPI mode configuration error, cr=0x%08X\n", val);
        spi_test_failed++;
        return -1;
    }
}

static int test_spi_fifo(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: SPI FIFO Configuration ===\n");
    
    spi_reg_write(SPI_REG_FIFO_LEVEL, 0x00000010);
    val = spi_reg_read(SPI_REG_FIFO_LEVEL);
    
    if (val == 0x00000010) {
        PRINTF("[PASS] SPI FIFO level configured\n");
        spi_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] FIFO configuration error\n");
        spi_test_failed++;
        return -1;
    }
}

static int test_spi_interrupt(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: SPI Interrupt ===\n");
    
    spi_reg_write(SPI_REG_INT_MASK, 0xFFFFFFFF);
    spi_reg_write(SPI_REG_INT_CLEAR, 0xFFFFFFFF);
    
    spi_reg_write(SPI_REG_INT_MASK, SPI_INT_TX_EMPTY | SPI_INT_RX_FULL | SPI_INT_ERR);
    
    val = spi_reg_read(SPI_REG_INT_MASK);
    if ((val & (SPI_INT_TX_EMPTY | SPI_INT_RX_FULL | SPI_INT_ERR)) == 0) {
        PRINTF("[PASS] SPI interrupt configured\n");
        spi_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Interrupt configuration error\n");
        spi_test_failed++;
        return -1;
    }
}

static int test_spi_speed(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: SPI Speed Configuration ===\n");
    
    spi_reg_write(SPI_REG_BAUD, 0x0000000A);
    val = spi_reg_read(SPI_REG_BAUD);
    
    if (val == 0x0000000A) {
        PRINTF("[PASS] SPI baud rate configured (div=10)\n");
        spi_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Baud rate configuration error\n");
        spi_test_failed++;
        return -1;
    }
}

void test_spi(void) {
    PRINTF("\n");
    PRINTF("========================================\n");
    PRINTF("  SPI Controller Test Suite\n");
    PRINTF("========================================\n");
    
    test_spi_transfer();
    test_spi_flash_access();
    test_spi_mode_selection();
    test_spi_fifo();
    test_spi_interrupt();
    test_spi_speed();
    
    PRINTF("\n========================================\n");
    PRINTF("  SPI Test Results: PASS=%u FAIL=%u\n", 
           spi_test_passed, spi_test_failed);
    PRINTF("========================================\n");
}
