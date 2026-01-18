// ============================================================================
// Module: soc_package
// Description: YaoGuang SoC 公共包定义
// Author: YaoGuang RTL Team
// Version: V1.0
// Date: 2026-01-18
// ============================================================================

package soc_package;

    // ============================================================================
    // 参数定义
    // ============================================================================
    
    // 芯片配置参数
    parameter int NUM_CPU_CORES            = 8;
    parameter int NUM_NPU_CLUSTERS         = 4;
    parameter int NUM_GPU_CORES            = 2;
    parameter int NUM_CAN_PORTS            = 8;
    parameter int NUM_I2C_PORTS            = 4;
    parameter int NUM_SPI_PORTS            = 4;
    parameter int NUM_UART_PORTS           = 8;
    parameter int NUM_GPIO_PINS            = 128;
    
    // 地址空间参数
    parameter int ADDR_WIDTH               = 32;
    parameter int DATA_WIDTH               = 64;
    parameter int AXI_DATA_WIDTH           = 512;
    parameter int AXI_ADDR_WIDTH           = 32;
    parameter int AXI_ID_WIDTH             = 8;
    parameter int AXI_USER_WIDTH           = 16;
    
    // NoC 参数
    parameter int NOC_NUM_PORTS            = 64;
    parameter int NOC_VC_COUNT             = 4;
    parameter int NOC_VC_WIDTH             = 2;
    
    // 缓存参数
    parameter int L1_ICACHE_SIZE           = 64;     // KB per core
    parameter int L1_DCACHE_SIZE           = 64;     // KB per core
    parameter int L2_CACHE_SIZE            = 512;    // KB per core
    parameter int L3_CACHE_SIZE            = 8192;   // KB total
    
    // 存储器参数
    parameter int DDR_DATA_WIDTH           = 32;
    parameter int DDR_BANK_COUNT           = 8;
    parameter int BOOT_ROM_SIZE            = 256;    // KB
    
    // 时钟参数
    parameter int CLK_CORE_FREQ            = 2000;   // MHz
    parameter int CLK_NPU_FREQ             = 2000;   // MHz
    parameter int CLK_GPU_FREQ             = 1500;   // MHz
    parameter int CLK_SYS_FREQ             = 1000;   // MHz
    parameter int CLK_DDR_FREQ             = 1600;   // MHz
    
    // 电源域参数
    parameter int NUM_POWER_DOMAINS        = 12;
    parameter int NUM_CLOCK_DOMAINS        = 12;
    parameter int NUM_RESET_DOMAINS        = 12;
    
    // 中断参数
    parameter int NUM_IRQ                  = 256;
    parameter int NUM_SGI                  = 16;
    parameter int NUM_PPI                  = 32;
    
    // ============================================================================
    // 地址映射常量
    // ============================================================================
    
    // 基础地址定义
    parameter logic [ADDR_WIDTH-1:0] ADDR_BOOT_ROM         = 32'h0000_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_SAFETY_ISLAND   = 32'h1000_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_NPU_CLUSTER0    = 32'h2000_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_NPU_CLUSTER1    = 32'h3000_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_NPU_CLUSTER2    = 32'h4000_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_NPU_CLUSTER3    = 32'h5000_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_L3_CACHE        = 32'h6000_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_GPU             = 32'h7000_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_ISP             = 32'h8000_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_DISPLAY         = 32'h9000_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_CRYPTO          = 32'hA000_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_PCIE_X8         = 32'hB000_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_PCIE_X4         = 32'hC000_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_USB             = 32'hD000_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_ETHERNET        = 32'hE000_0000;
    
    // APB 外设基地址
    parameter logic [ADDR_WIDTH-1:0] ADDR_APB_PERIPH_BASE = 32'hF000_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_PMU             = 32'hF000_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_CLOCK_RESET     = 32'hF100_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_ERROR_REPORT    = 32'hF200_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_DEBUG           = 32'hF300_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_GIC             = 32'hF400_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_SYSTEM_TIMER    = 32'hF500_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_WATCHDOG        = 32'hF600_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_RTC             = 32'hF700_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_GPIO            = 32'hF800_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_I2C_BASE        = 32'hFA00_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_SPI_BASE        = 32'hFB00_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_UART_BASE       = 32'hFC00_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_CAN_BASE        = 32'hFD00_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_AUDIO           = 32'hFE00_0000;
    parameter logic [ADDR_WIDTH-1:0] ADDR_DDR_CTRL        = 32'hFF00_0000;
    
    // 地址掩码
    parameter logic [ADDR_WIDTH-1:0] ADDR_MASK_256MB      = 32'h0FFF_FFFF;
    parameter logic [ADDR_WIDTH-1:0] ADDR_MASK_16MB       = 32'h00FF_FFFF;
    parameter logic [ADDR_WIDTH-1:0] ADDR_MASK_4KB        = 32'h0000_0FFF;
    
    // ============================================================================
    // 时钟定义
    // ============================================================================
    
    typedef enum int {
        CLK_IDX_CORE      = 0,
        CLK_IDX_SAFETY    = 1,
        CLK_IDX_NPU       = 2,
        CLK_IDX_GPU       = 3,
        CLK_IDX_ISP       = 4,
        CLK_IDX_NOC       = 5,
        CLK_IDX_MEM       = 6,
        CLK_IDX_SYS       = 7,
        CLK_IDX_USB       = 8,
        CLK_IDX_PCIE      = 9,
        CLK_IDX_ETH       = 10,
        CLK_IDX_RTC       = 11
    } clock_domain_idx_t;
    
    // ============================================================================
    // 复位定义
    // ============================================================================
    
    typedef enum int {
        RST_IDX_POR       = 0,
        RST_IDX_CORE      = 1,
        RST_IDX_SAFETY    = 2,
        RST_IDX_NPU       = 3,
        RST_IDX_GPU       = 4,
        RST_IDX_ISP       = 5,
        RST_IDX_NOC       = 6,
        RST_IDX_MEM       = 7,
        RST_IDX_SYS       = 8,
        RST_IDX_PCIE      = 9,
        RST_IDX_USB       = 10,
        RST_IDX_ETH       = 11
    } reset_domain_idx_t;
    
    // ============================================================================
    // 电源域定义
    // ============================================================================
    
    typedef enum int {
        PD_IDX_ALWAYS_ON  = 0,
        PD_IDX_CPU        = 1,
        PD_IDX_SAFETY     = 2,
        PD_IDX_NPU        = 3,
        PD_IDX_GPU        = 4,
        PD_IDX_ISP        = 5,
        PD_IDX_NOC        = 6,
        PD_IDX_MEM        = 7,
        PD_IDX_SYS        = 8,
        PD_IDX_PCIE       = 9,
        PD_IDX_USB        = 10,
        PD_IDX_ETH        = 11
    } power_domain_idx_t;
    
    // ============================================================================
    // 电源状态定义
    // ============================================================================
    
    typedef enum logic [1:0] {
        PWR_STATE_ON       = 2'b00,
        PWR_STATE_RETENTION = 2'b01,
        PWR_STATE_OFF      = 2'b10,
        PWR_STATE_RESERVED = 2'b11
    } power_state_t;
    
    // ============================================================================
    // 中断定义
    // ============================================================================
    
    typedef enum int {
        IRQ_CPU0          = 0,
        IRQ_CPU1          = 1,
        IRQ_CPU2          = 2,
        IRQ_CPU3          = 3,
        IRQ_CPU4          = 4,
        IRQ_CPU5          = 5,
        IRQ_CPU6          = 6,
        IRQ_CPU7          = 7,
        IRQ_SAFETY        = 8,
        IRQ_NPU0          = 9,
        IRQ_NPU1          = 10,
        IRQ_NPU2          = 11,
        IRQ_NPU3          = 12,
        IRQ_GPU           = 13,
        IRQ_ISP           = 14,
        IRQ_DISPLAY       = 15,
        IRQ_PCIE          = 16,
        IRQ_USB           = 17,
        IRQ_ETH           = 18,
        IRQ_CAN           = 19,
        IRQ_I2C           = 20,
        IRQ_SPI           = 21,
        IRQ_UART          = 22,
        IRQ_GPIO          = 23,
        IRQ_TIMER         = 24,
        IRQ_WATCHDOG      = 25,
        IRQ_RTC           = 26,
        IRQ_AUDIO         = 27,
        IRQ_CRYPTO        = 28,
        IRQ_DDR           = 29,
        IRQ_ERROR         = 30,
        IRQ_SOFT          = 31
    } irq_idx_t;
    
    // ============================================================================
    // 错误类型定义
    // ============================================================================
    
    typedef enum logic [3:0] {
        ERR_NONE          = 4'b0000,
        ERR_ADDR_DECODE   = 4'b0001,
        ERR_TIMEOUT       = 4'b0010,
        ERR_PARITY        = 4'b0011,
        ERR_ECC           = 4'b0100,
        ERR_ACCESS        = 4'b0101,
        ERR_SECURITY      = 4'b0110,
        ERR_CRC           = 4'b0111,
        ERR_PROTOCOL      = 4'b1000,
        ERR_FATAL         = 4'b1111
    } error_type_t;
    
    // ============================================================================
    // NoC QoS 定义
    // ============================================================================
    
    typedef enum logic [1:0] {
        QoS_LOW           = 2'b00,
        QoS_MEDIUM        = 2'b01,
        QoS_HIGH          = 2'b10,
        QoS_CRITICAL      = 2'b11
    } qos_level_t;
    
    // ============================================================================
    // 启动模式定义
    // ============================================================================
    
    typedef enum logic [2:0] {
        BOOT_QSPI         = 3'b000,
        BOOT_EMMC         = 3'b001,
        BOOT_NOR          = 3'b010,
        BOOT_UART         = 3'b011,
        BOOT_USB          = 3'b100,
        BOOT_RESERVED     = 3'b111
    } boot_mode_t;
    
    // ============================================================================
    // 调试类型定义
    // ============================================================================
    
    typedef enum logic [1:0] {
        DBG_MODE_NORMAL   = 2'b00,
        DBG_MODE_HALT     = 2'b01,
        DBG_MODE_STEP     = 2'b10,
        DBG_MODE_RESET    = 2'b11
    } debug_mode_t;
    
    // ============================================================================
    // 通用结构体定义
    // ============================================================================
    
    // 时钟配置结构
    typedef struct {
        logic             enable;
        logic [31:0]      frequency;
        logic             div_valid;
        logic [7:0]       div_value;
    } clock_config_t;
    
    // 复位配置结构
    typedef struct {
        logic             assert_n;
        logic             sync;
        logic             deassert_done;
    } reset_config_t;
    
    // 电源配置结构
    typedef struct {
        power_state_t     state;
        logic             gate_enable;
        logic             retention_enable;
        logic [7:0]       voltage;
    } power_config_t;
    
    // 错误报告结构
    typedef struct {
        error_type_t      err_type;
        logic [ADDR_WIDTH-1:0] err_addr;
        logic [7:0]       err_master;
        logic             err_valid;
        logic             err_fatal;
    } error_info_t;
    
    // 中断信息结构
    typedef struct {
        logic             irq_valid;
        logic [7:0]       irq_id;
        logic             irq_type;  // 0: edge, 1: level
        logic             irq_polarity;  // 0: low, 1: high
    } irq_info_t;
    
endpackage
