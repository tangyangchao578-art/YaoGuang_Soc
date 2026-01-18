#include "test_framework.h"
#include "usb_hw.h"

#define USB_BASE_ADDR  0x40040000

static uint32_t usb_test_passed = 0;
static uint32_t usb_test_failed = 0;

static void usb_reg_write(uint32_t offset, uint32_t value) {
    volatile uint32_t *reg = (volatile uint32_t *)(USB_BASE_ADDR + offset);
    *reg = value;
}

static uint32_t usb_reg_read(uint32_t offset) {
    volatile uint32_t *reg = (volatile uint32_t *)(USB_BASE_ADDR + offset);
    return *reg;
}

static int test_usb_device_enumeration(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: USB Device Enumeration ===\n");
    
    usb_reg_write(USB_REG_CTRL, USB_CTRL_HOST_MODE);
    delay_ms(50);
    
    usb_reg_write(USB_REG_PORT_CR, USB_PORT_CR_RESET);
    delay_ms(100);
    usb_reg_write(USB_REG_PORT_CR, 0);
    
    val = usb_reg_read(USB_REG_PORT_SR);
    if (val & USB_PORT_SR_ATTACHED) {
        uint32_t speed = usb_reg_read(USB_REG_PORT_SR) & USB_PORT_SR_SPEED;
        PRINTF("[PASS] Device attached, speed=%s\n",
               speed == USB_PORT_SR_HS ? "High-Speed" : 
               speed == USB_PORT_SR_FS ? "Full-Speed" : "Low-Speed");
        usb_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] No device attached, sr=0x%08X\n", val);
        usb_test_failed++;
        return -1;
    }
}

static int test_usb_control_transfer(void) {
    uint32_t val;
    uint8_t setup_data[8] = {
        0x80, 0x06, 0x00, 0x01, 0x00, 0x00, 0x40, 0x00
    };
    
    PRINTF("\n=== Test: USB Control Transfer ===\n");
    
    for (int i = 0; i < 8; i += 4) {
        uint32_t data = setup_data[i] | (setup_data[i+1] << 8) | 
                       (setup_data[i+2] << 16) | (setup_data[i+3] << 24);
        usb_reg_write(USB_REG_EP0_TX, data);
    }
    
    usb_reg_write(USB_REG_EP0_CR, USB_EP_CR_TX_LEN | USB_EP_CR_STATUS_PHASE);
    
    delay_ms(10);
    val = usb_reg_read(USB_REG_EP0_SR);
    
    if (val & USB_EP_SR_TX_SUCCESS) {
        PRINTF("[PASS] Control transfer completed\n");
        usb_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Control transfer failed, sr=0x%08X\n", val);
        usb_test_failed++;
        return -1;
    }
}

static int test_usb_bulk_transfer(void) {
    uint32_t val;
    uint32_t ep = 1;
    
    PRINTF("\n=== Test: USB Bulk Transfer ===\n");
    
    usb_reg_write(USB_REG_EP_TX_LEN(ep), 512);
    usb_reg_write(USB_REG_EP_CR(ep), USB_EP_CR_TX_START);
    
    delay_ms(50);
    val = usb_reg_read(USB_REG_EP_SR(ep));
    
    if (val & USB_EP_SR_TX_SUCCESS) {
        uint32_t bytes = usb_reg_read(USB_REG_EP_TX_COUNT(ep));
        PRINTF("[PASS] Bulk transfer completed, bytes=%u\n", bytes);
        usb_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Bulk transfer failed, sr=0x%08X\n", val);
        usb_test_failed++;
        return -1;
    }
}

static int test_usb_interrupt(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: USB Interrupt Handling ===\n");
    
    usb_reg_write(USB_REG_INT_MASK, 0xFFFFFFFF);
    usb_reg_write(USB_REG_INT_CLEAR, 0xFFFFFFFF);
    
    usb_reg_write(USB_REG_INT_MASK, USB_INT_SUSPEND | USB_INT_RESUME | USB_INT_RESET);
    
    val = usb_reg_read(USB_REG_INT_STATUS);
    usb_reg_write(USB_REG_INT_CLEAR, val);
    
    if ((val & (USB_INT_SUSPEND | USB_INT_RESUME | USB_INT_RESET)) == 0 ||
        (val & USB_INT_RESET)) {
        PRINTF("[PASS] Interrupt handling configured\n");
        usb_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Unexpected interrupt, status=0x%08X\n", val);
        usb_test_failed++;
        return -1;
    }
}

static int test_usb_endpoint(void) {
    uint32_t val;
    
    PRINTF("\n=== Test: USB Endpoint Configuration ===\n");
    
    usb_reg_write(USB_REG_EP_CFG(0), USB_EP_CFG_VALID | USB_EP_TYPE_CONTROL | 64);
    usb_reg_write(USB_REG_EP_CFG(1), USB_EP_CFG_VALID | USB_EP_TYPE_BULK | 512);
    usb_reg_write(USB_REG_EP_CFG(2), USB_EP_CFG_VALID | USB_EP_TYPE_INT | 64);
    
    val = usb_reg_read(USB_REG_EP_CFG(0)) & (USB_EP_CFG_VALID | USB_EP_TYPE_MASK);
    if (val == (USB_EP_CFG_VALID | USB_EP_TYPE_CONTROL)) {
        PRINTF("[PASS] Endpoints configured correctly\n");
        usb_test_passed++;
        return 0;
    } else {
        PRINTF("[FAIL] Endpoint configuration error, cfg=0x%08X\n", val);
        usb_test_failed++;
        return -1;
    }
}

void test_usb(void) {
    PRINTF("\n");
    PRINTF("========================================\n");
    PRINTF("  USB Controller Test Suite\n");
    PRINTF("========================================\n");
    
    test_usb_device_enumeration();
    test_usb_control_transfer();
    test_usb_bulk_transfer();
    test_usb_interrupt();
    test_usb_endpoint();
    
    PRINTF("\n========================================\n");
    PRINTF("  USB Test Results: PASS=%u FAIL=%u\n", 
           usb_test_passed, usb_test_failed);
    PRINTF("========================================\n");
}
