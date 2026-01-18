#include "test_framework.h"
#include "ethernet_hw.h"

#define ETH_BASE_ADDR  0x40030000

static uint32_t eth_test_passed = 0;
static uint32_t eth_test_failed = 0;

static void eth_reg_write(uint32_t offset, uint32_t value) {
    volatile uint32_t *reg = (volatile uint32_t *)(ETH_BASE_ADDR + offset);
    *reg = value;
}

static uint32_t eth_reg_read(uint32_t offset) {
    volatile uint32_t *reg = (volatile uint32_t *)(ETH_BASE_ADDR + offset);
    return *reg;
}

static int test_eth_mac_init(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: Ethernet MAC Initialization ===\n");
    
    eth_reg_write(ETH_REG_MAC_CR, ETH_MAC_CR_SOFT_RST);
    delay_ms(10);
    eth_reg_write(ETH_REG_MAC_CR, ETH_MAC_CR_TX_EN | ETH_MAC_CR_RX_EN);
    
    val = eth_reg_read(ETH_REG_MAC_CR);
    if ((val & (ETH_MAC_CR_TX_EN | ETH_MAC_CR_RX_EN)) == 
        (ETH_MAC_CR_TX_EN | ETH_MAC_CR_RX_EN)) {
        PRINTF("[PASS] MAC initialized and enabled\n");
        eth_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] MAC not properly initialized, cr=0x%08X\n", val);
        eth_test_failed++;
        return -1;
    }
}

static int test_eth_phy_auto_negotiation(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: PHY Auto-Negotiation ===\n");
    
    eth_reg_write(ETH_REG_PHY_CR, ETH_PHY_CR_AUTO_NEG);
    delay_ms(100);
    
    val = eth_reg_read(ETH_REG_PHY_SR);
    if (val & ETH_PHY_SR_AN_COMPLETE) {
        uint32_t speed = eth_reg_read(ETH_REG_PHY_SR) & ETH_PHY_SR_SPEED;
        PRINTF("[PASS] Auto-negotiation complete, speed=%s\n", 
               speed == ETH_PHY_SR_1000M ? "1Gbps" : 
               speed == ETH_PHY_SR_100M ? "100Mbps" : "10Mbps");
        eth_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Auto-negotiation not complete, sr=0x%08X\n", val);
        eth_test_failed++;
        return -1;
    }
}

static int test_eth_frame_transmit(void) {
    uint32_t val;
    uint8_t tx_frame[] = {
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0x00, 0x11, 0x22, 0x33, 0x44, 0x55,
        0x08, 0x00,
        0x45, 0x00, 0x00, 0x2C, 0x00, 0x00, 0x40, 0x00,
        0x40, 0x11, 0x00, 0x00, 0xC0, 0xA8, 0x01, 0x64,
        0xC0, 0xA8, 0x01, 0x01, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
    };
    
    PRINTF("\n=== Test: Ethernet Frame Transmit ===\n");
    
    eth_reg_write(ETH_REG_TX_CR, ETH_TX_CR_START);
    
    for (int i = 0; i < sizeof(tx_frame); i += 4) {
        uint32_t data = tx_frame[i] | (tx_frame[i+1] << 8) | 
                       (tx_frame[i+2] << 16) | (tx_frame[i+3] << 24);
        eth_reg_write(ETH_REG_TX_DATA, data);
    }
    
    eth_reg_write(ETH_REG_TX_CR, ETH_TX_CR_START | ETH_TX_CR_TX);
    
    delay_ms(10);
    val = eth_reg_read(ETH_REG_TX_CR);
    
    if (!(val & ETH_TX_CR_TX)) {
        PRINTF("[PASS] Frame transmitted successfully\n");
        eth_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Frame transmission in progress or failed\n");
        eth_test_failed++;
        return -1;
    }
}

static int test_eth_frame_receive(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: Ethernet Frame Receive ===\n");
    
    val = eth_reg_read(ETH_REG_RX_STATUS);
    if (val & ETH_RX_STATUS_FRAME_RDY) {
        uint32_t frame_len = eth_reg_read(ETH_REG_RX_LEN);
        PRINTF("[PASS] Frame received, length=%u bytes\n", frame_len);
        eth_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] No frame received\n");
        eth_test_failed++;
        return -1;
    }
}

static int test_eth_dma(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: Ethernet DMA ===\n");
    
    eth_reg_write(ETH_REG_DMA_CR, ETH_DMA_CR_RX_START | ETH_DMA_CR_TX_START);
    val = eth_reg_read(ETH_REG_DMA_SR);
    
    if ((val & (ETH_DMA_SR_RX_BUSY | ETH_DMA_SR_TX_BUSY)) == 0) {
        PRINTF("[PASS] DMA channels configured\n");
        eth_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] DMA busy, sr=0x%08X\n", val);
        eth_test_failed++;
        return -1;
    }
}

void test_ethernet(void) {
    PRINTF("\n");
    PRINTF("========================================\n");
    PRINTF("  Ethernet Controller Test Suite\n");
    PRINTF("========================================\n");
    
    test_eth_mac_init();
    test_eth_phy_auto_negotiation();
    test_eth_frame_transmit();
    test_eth_frame_receive();
    test_eth_dma();
    
    PRINTF("\n========================================\n");
    PRINTF("  Ethernet Test Results: PASS=%u FAIL=%u\n", 
           eth_test_passed, eth_test_failed);
    PRINTF("========================================\n");
}
