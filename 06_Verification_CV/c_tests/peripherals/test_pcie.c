#include "test_framework.h"
#include "pcie_hw.h"

#define PCIE_BASE_ADDR  0x40020000

static uint32_t pcie_test_passed = 0;
static uint32_t pcie_test_failed = 0;

static void pcie_reg_write(uint32_t offset, uint32_t value) {
    volatile uint32_t *reg = (volatile uint32_t *)(PCIE_BASE_ADDR + offset);
    *reg = value;
}

static uint32_t pcie_reg_read(uint32_t offset) {
    volatile uint32_t *reg = (volatile uint32_t *)(PCIE_BASE_ADDR + offset);
    return *reg;
}

static int test_pcie_link_training(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: PCIe Link Training ===\n");
    
    pcie_reg_write(PCIE_REG_CTRL, PCIE_CTRL_RESET);
    delay_ms(100);
    pcie_reg_write(PCIE_REG_CTRL, PCIE_CTRL_LINK_UP);
    
    val = pcie_reg_read(PCIE_REG_STATUS);
    if (val & PCIE_STATUS_LINK_UP) {
        PRINTF("[PASS] PCIe link established\n");
        pcie_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] PCIe link not established, status=0x%08X\n", val);
        pcie_test_failed++;
        return -1;
    }
}

static int test_pcie_enumeration(void) {
    uint32_t val, bus, dev, func;
    
    PRINTF("\n=== Test: PCIe Enumeration ===\n");
    
    pcie_reg_write(PCIE_REG_ENUM_START, 1);
    
    val = pcie_reg_read(PCIE_REG_ENUM_DONE);
    if (val) {
        bus = pcie_reg_read(PCIE_REG_ENUM_BUS);
        dev = pcie_reg_read(PCIE_REG_ENUM_DEV);
        func = pcie_reg_read(PCIE_REG_ENUM_FUNC);
        PRINTF("[PASS] Enumeration complete: BDF=0x%02X:%02X.%X\n", bus, dev, func);
        pcie_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Enumeration not complete\n");
        pcie_test_failed++;
        return -1;
    }
}

static int test_pcie_dma(void) {
    uint32_t val;
    uint64_t src_addr = 0x80000000;
    uint64_t dst_addr = 0x90000000;
    uint32_t size = 0x1000;
    
    PRINTF("\n=== Test: PCIe DMA Transfer ===\n");
    
    pcie_reg_write(PCIE_REG_DMA_SRC_L, src_addr & 0xFFFFFFFF);
    pcie_reg_write(PCIE_REG_DMA_SRC_H, src_addr >> 32);
    pcie_reg_write(PCIE_REG_DMA_DST_L, dst_addr & 0xFFFFFFFF);
    pcie_reg_write(PCIE_REG_DMA_DST_H, dst_addr >> 32);
    pcie_reg_write(PCIE_REG_DMA_SIZE, size);
    pcie_reg_write(PCIE_REG_DMA_CTRL, PCIE_DMA_START);
    
    while (1) {
        val = pcie_reg_read(PCIE_REG_DMA_STATUS);
        if (val & PCIE_DMA_DONE) {
            PRINTF("[PASS] DMA transfer complete\n");
            pcie_test_passed++;
            return 0;
        }
        if (val & PCIE_DMA_ERROR) {
            PRINTF("[FAIL] DMA transfer error\n");
            pcie_test_failed++;
            return -1;
        }
    }
}

static int test_pcie_interrupt(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: PCIe Interrupt ===\n");
    
    pcie_reg_write(PCIE_REG_INT_MASK, 0xFFFFFFFF);
    pcie_reg_write(PCIE_REG_INT_CLEAR, 0xFFFFFFFF);
    
    pcie_reg_write(PCIE_REG_INT_MASK, PCIE_INT_MSI | PCIE_INT_LINK);
    
    val = pcie_reg_read(PCIE_REG_INT_STATUS);
    pcie_reg_write(PCIE_REG_INT_CLEAR, val);
    
    if ((val & (PCIE_INT_MSI | PCIE_INT_LINK)) == 0) {
        PRINTF("[PASS] Interrupt handling works\n");
        pcie_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Unexpected interrupt status=0x%08X\n", val);
        pcie_test_failed++;
        return -1;
    }
}

void test_pcie(void) {
    PRINTF("\n");
    PRINTF("========================================\n");
    PRINTF("  PCIe Controller Test Suite\n");
    PRINTF("========================================\n");
    
    test_pcie_link_training();
    test_pcie_enumeration();
    test_pcie_dma();
    test_pcie_interrupt();
    
    PRINTF("\n========================================\n");
    PRINTF("  PCIe Test Results: PASS=%u FAIL=%u\n", 
           pcie_test_passed, pcie_test_failed);
    PRINTF("========================================\n");
}
