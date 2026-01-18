#include "test_framework.h"
#include "can_hw.h"

#define CAN_BASE_ADDR  0x40050000

static uint32_t can_test_passed = 0;
static uint32_t can_test_failed = 0;

static void can_reg_write(uint32_t offset, uint32_t value) {
    volatile uint32_t *reg = (volatile uint32_t *)(CAN_BASE_ADDR + offset);
    *reg = value;
}

static uint32_t can_reg_read(uint32_t offset) {
    volatile uint32_t *reg = (volatile uint32_t *)(CAN_BASE_ADDR + offset);
    return *reg;
}

static int test_can_transmit(void) {
    uint32_t val;
    uint32_t msg_id = 0x123;
    uint8_t msg_data[8] = {0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08};
    
    PRINTF("\n=== Test: CAN Message Transmit ===\n");
    
    can_reg_write(CAN_REG_TX_ID, msg_id | CAN_IDE_STD);
    can_reg_write(CAN_REG_TX_DLC, 8);
    
    for (int i = 0; i < 8; i += 4) {
        uint32_t data = msg_data[i] | (msg_data[i+1] << 8) | 
                       (msg_data[i+2] << 16) | (msg_data[i+3] << 24);
        can_reg_write(CAN_REG_TX_DATA, data);
    }
    
    can_reg_write(CAN_REG_TX_CR, CAN_TX_CR_START);
    
    delay_ms(1);
    val = can_reg_read(CAN_REG_TX_SR);
    
    if (val & CAN_TX_SR_SUCCESS) {
        PRINTF("[PASS] Message transmitted, id=0x%X\n", msg_id);
        can_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Message transmit pending/failed, sr=0x%08X\n", val);
        can_test_failed++;
        return -1;
    }
}

static int test_can_receive(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: CAN Message Receive ===\n");
    
    val = can_reg_read(CAN_REG_RX_SR);
    if (val & CAN_RX_SR_RDY) {
        uint32_t msg_id = can_reg_read(CAN_REG_RX_ID);
        uint32_t dlc = can_reg_read(CAN_REG_RX_DLC);
        PRINTF("[PASS] Message received, id=0x%X, dlc=%u\n", msg_id & 0x7FF, dlc);
        can_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] No message received, sr=0x%08X\n", val);
        can_test_failed++;
        return -1;
    }
}

static int test_can_bitrate_switch(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: CAN FD Bitrate Switch ===\n");
    
    can_reg_write(CAN_REG_BTR, CAN_BTR_BRP(10) | CAN_BTR_TSEG1(5) | CAN_BTR_TSEG2(2));
    can_reg_write(CAN_REG_BTR_FD, CAN_BTR_FD_BRP(5) | CAN_BTR_FD_TSEG1(7) | CAN_BTR_FD_TSEG2(3));
    
    val = can_reg_read(CAN_REG_BTR);
    if ((val & CAN_BTR_BRP_MASK) == CAN_BTR_BRP(10)) {
        PRINTF("[PASS] Bitrate configured (nominal: 500K, FD: 2M)\n");
        can_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Bitrate configuration error, btr=0x%08X\n", val);
        can_test_failed++;
        return -1;
    }
}

static int test_can_filter(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: CAN Acceptance Filter ===\n");
    
    can_reg_write(CAN_REG_AF_ACR(0), 0x100);
    can_reg_write(CAN_REG_AF_AMR(0), 0x700);
    
    val = can_reg_read(CAN_REG_AF_ACR(0));
    if (val == 0x100) {
        PRINTF("[PASS] Acceptance filter configured\n");
        can_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Filter configuration error, acr=0x%08X\n", val);
        can_test_failed++;
        return -1;
    }
}

static int test_can_fd_mode(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: CAN FD Mode ===\n");
    
    can_reg_write(CAN_REG_CR, CAN_CR_FD_ENABLE | CAN_CR_ISO);
    
    val = can_reg_read(CAN_REG_CR);
    if (val & CAN_CR_FD_ENABLE) {
        PRINTF("[PASS] CAN FD mode enabled\n");
        can_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] CAN FD mode not enabled, cr=0x%08X\n", val);
        can_test_failed++;
        return -1;
    }
}

void test_can(void) {
    PRINTF("\n");
    PRINTF("========================================\n");
    PRINTF("  CAN FD Controller Test Suite\n");
    PRINTF("========================================\n");
    
    test_can_transmit();
    test_can_receive();
    test_can_bitrate_switch();
    test_can_filter();
    test_can_fd_mode();
    
    PRINTF("\n========================================\n");
    PRINTF("  CAN Test Results: PASS=%u FAIL=%u\n", 
           can_test_passed, can_test_failed);
    PRINTF("========================================\n");
}
