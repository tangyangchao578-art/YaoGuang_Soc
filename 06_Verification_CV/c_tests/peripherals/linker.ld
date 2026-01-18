OUTPUT_ARCH(riscv)
ENTRY(_start)

MEMORY {
    flash (rxai) : ORIGIN = 0x80000000, LENGTH = 16M
    ram (waxi)   : ORIGIN = 0x90000000, LENGTH = 4M
}

SECTIONS {
    .text : {
        *(.text*)
    } > flash
    
    .rodata : {
        *(.rodata*)
    } > flash
    
    .data : {
        *(.data*)
    } > ram
    
    .bss : {
        *(.bss*)
        *(COMMON)
    } > ram
}
