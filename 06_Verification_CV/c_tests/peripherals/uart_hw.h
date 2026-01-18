#ifndef UART_HW_H
#define UART_HW_H

#include <stdint.h>

#define UART_BASE_ADDR  0x40090000

#define UART_REG_RBR            0x0000
#define UART_REG_THR            0x0000
#define UART_REG_DLL            0x0000
#define UART_REG_IER            0x0004
#define UART_REG_DLM            0x0004
#define UART_REG_IIR            0x0008
#define UART_REG_FCR            0x0008
#define UART_REG_LCR            0x000C
#define UART_REG_MCR            0x0010
#define UART_REG_LSR            0x0014
#define UART_REG_MSR            0x0018
#define UART_REG_SCR            0x001C

#define UART_LCR_DLAB           0x00000080
#define UART_LCR_8N1            0x00000003
#define UART_LCR_7E1            0x0000001A
#define UART_LCR_7O1            0x0000000A
#define UART_FCR_ENABLE         0x00000001
#define UART_FCR_TRIGGER_8      0x00000000
#define UART_FCR_TRIGGER_16     0x00000040
#define UART_FCR_TRIGGER_32     0x00000080
#define UART_FCR_TRIGGER_56     0x000000C0
#define UART_IER_RDA            0x00000001
#define UART_IER_THRE           0x00000002
#define UART_IER_RLS            0x00000004
#define UART_MCR_DTR            0x00000001
#define UART_MCR_RTS            0x00000002
#define UART_LSR_THRE           0x00000020
#define UART_LSR_DR             0x00000001

void test_uart(void);

#endif
