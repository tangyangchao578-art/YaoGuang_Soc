#ifndef USB_HW_H
#define USB_HW_H

#include <stdint.h>

#define USB_BASE_ADDR  0x40040000

#define USB_REG_CTRL           0x0000
#define USB_REG_PORT_CR        0x0004
#define USB_REG_PORT_SR        0x0008
#define USB_REG_EP0_CR         0x0100
#define USB_REG_EP0_SR         0x0104
#define USB_REG_EP0_TX         0x0108
#define USB_REG_EP0_RX         0x010C
#define USB_REG_EP0_CFG        0x0110
#define USB_REG_INT_STATUS     0x0200
#define USB_REG_INT_MASK       0x0204
#define USB_REG_INT_CLEAR      0x0208

#define USB_CTRL_HOST_MODE     0x00000001
#define USB_PORT_CR_RESET      0x00000001
#define USB_PORT_SR_ATTACHED   0x00000001
#define USB_PORT_SR_SPEED      0x00000006
#define USB_PORT_SR_HS         0x00000002
#define USB_PORT_SR_FS         0x00000000
#define USB_PORT_SR_LS         0x00000004
#define USB_EP_CR_TX_LEN       0x00000100
#define USB_EP_CR_TX_START     0x00000001
#define USB_EP_CR_STATUS_PHASE 0x00000002
#define USB_EP_SR_TX_SUCCESS   0x00000001
#define USB_EP_CFG_VALID       0x00000001
#define USB_EP_TYPE_CONTROL    0x00000000
#define USB_EP_TYPE_BULK       0x00000002
#define USB_EP_TYPE_INT        0x00000004
#define USB_INT_SUSPEND        0x00000001
#define USB_INT_RESUME         0x00000002
#define USB_INT_RESET          0x00000004

void test_usb(void);

#endif
