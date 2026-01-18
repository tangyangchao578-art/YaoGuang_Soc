# YaoGuang SoC Peripheral Test Makefile
# CV Verification - System Level Tests

CC      = riscv64-unknown-elf-gcc
OBJDUMP = riscv64-unknown-elf-objdump
OBJCOPY = riscv64-unknown-elf-objcopy

CFLAGS  = -march=rv64imafdc -mabi=lp64 -O2 -Wall -I.
LDFLAGS = -T linker.ld -nostdlib

SRCS    = peripherals_test.c
OBJS    = $(SRCS:.c=.o)

TARGET  = peripherals_test.elf

.PHONY: all clean run dump

all: $(TARGET)

$(TARGET): $(OBJS)
	$(CC) $(LDFLAGS) -o $@ $^

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

run: $(TARGET)
	@echo "Run on QEMU or FPGA platform"

dump: $(TARGET)
	$(OBJDUMP) -D -b binary $< > $<.dis

clean:
	rm -f $(OBJS) $(TARGET) *.dis

install:
	cp $(TARGET) ../build/
