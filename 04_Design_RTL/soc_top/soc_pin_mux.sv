// ============================================================================
// Module: soc_pin_mux
// Description: YaoGuang SoC 引脚复用控制
// Author: YaoGuang RTL Team
// Version: V1.0
// Date: 2026-01-18
// ============================================================================

`timescale 1ns / 1ps

module soc_pin_mux (
    // ============================================================================
    // 时钟与复位
    // ============================================================================
    
    input  logic                         clk,
    input  logic                         rst_n,
    
    // ============================================================================
    // APB 接口 (配置寄存器)
    // ============================================================================
    
    input  logic                         psel,
    input  logic                         penable,
    input  logic [31:0]                  paddr,
    input  logic                         pwrite,
    input  logic [31:0]                  pwdata,
    output logic [31:0]                  prdata,
    output logic                         pslverr,
    output logic                         pready,
    
    // ============================================================================
    // 模式选择输入
    // ============================================================================
    
    input  logic [2:0]                   boot_mode,        // 启动模式
    input  logic [3:0]                   func_sel [128],   // 功能选择
    
    // ============================================================================
    // 物理引脚接口
    // ============================================================================
    
    // GPIO 双向引脚
    inout  wire [127:0]                  gpio_pin,
    
    // I2C 引脚
    inout  wire [7:0]                    i2c_scl_pin,
    inout  wire [7:0]                    i2c_sda_pin,
    
    // SPI 引脚
    output logic [7:0]                   spi_sclk_pin,
    output logic [7:0]                   spi_mosi_pin,
    input  logic [7:0]                   spi_miso_pin,
    output logic [7:0]                   spi_cs_n_pin,
    
    // UART 引脚
    output logic [7:0]                   uart_tx_pin,
    input  logic [7:0]                   uart_rx_pin,
    
    // JTAG 调试引脚
    input  logic                         jtag_tck_pin,
    input  logic                         jtag_tms_pin,
    input  logic                         jtag_tdi_pin,
    output logic                         jtag_tdo_pin,
    input  logic                         jtag_trst_n_pin,
    
    // ============================================================================
    // 内部逻辑接口
    // ============================================================================
    
    // GPIO 接口
    output logic [127:0]                 gpio_o,
    output logic [127:0]                 gpio_oe,
    input  logic [127:0]                 gpio_i,
    
    // I2C 接口
    output logic [7:0]                   i2c_scl_o,
    output logic [7:0]                   i2c_scl_oe,
    input  logic [7:0]                   i2c_scl_i,
    output logic [7:0]                   i2c_sda_o,
    output logic [7:0]                   i2c_sda_oe,
    input  logic [7:0]                   i2c_sda_i,
    
    // SPI 接口
    output logic [7:0]                   spi_sclk_o,
    output logic [7:0]                   spi_mosi_o,
    input  logic [7:0]                   spi_miso_i,
    output logic [7:0]                   spi_cs_n_o,
    
    // UART 接口
    output logic [7:0]                   uart_tx_o,
    input  logic [7:0]                   uart_rx_i,
    
    // JTAG 接口
    input  logic                         jtag_tck_i,
    input  logic                         jtag_tms_i,
    input  logic                         jtag_tdi_i,
    output logic                         jtag_tdo_o,
    input  logic                         jtag_trst_n_i,
    
    // Debug 接口
    output logic                         dbg_req,
    input  logic                         dbg_ack
);
    
    // ============================================================================
    // 参数定义
    // ============================================================================
    
    parameter int NUM_GPIOS              = 128;
    parameter int NUM_I2C                = 8;
    parameter int NUM_SPI                = 8;
    parameter int NUM_UART               = 8;
    parameter int NUM_MODES              = 16;
    
    // 引脚功能定义
    typedef enum logic [3:0] {
        FUNC_GPIO      = 4'h0,
        FUNC_UART      = 4'h1,
        FUNC_I2C       = 4'h2,
        FUNC_SPI       = 4'h3,
        FUNC_PWM       = 4'h4,
        FUNC_CAN       = 4'h5,
        FUNC_I2S       = 4'h6,
        FUNC_JTAG      = 4'h7,
        FUNC_RESERVED  = 4'hF
    } pin_function_t;
    
    // ============================================================================
    // 寄存器定义
    // ============================================================================
    
    logic [31:0]                         reg_gpio_dir [128];    // 方向控制
    logic [31:0]                         reg_gpio_out [128];    // 输出值
    logic [31:0]                         reg_gpio_pull [128];   // 上拉/下拉
    logic [31:0]                         reg_func_sel [128];    // 功能选择
    logic [31:0]                         reg_mux_ctrl;          // 复用控制
    logic [31:0]                         reg_pin_status;        // 引脚状态
    logic [31:0]                         reg_int_enable;        // 中断使能
    logic [31:0]                         reg_int_status;        // 中断状态
    logic [31:0]                         reg_int_polarity;      // 中断极性
    
    // ============================================================================
    // APB 从设备逻辑
    // ============================================================================
    
    always_comb begin
        prdata    = 32'h0000_0000;
        pslverr   = 1'b0;
        pready    = 1'b1;
        
        if (psel && penable) begin
            if (pwrite) begin
                // 写操作
                case (paddr[11:2])
                    10'h000: reg_gpio_dir[paddr[9:2]]  = pwdata;
                    10'h001: reg_gpio_out[paddr[9:2]]  = pwdata;
                    10'h002: reg_gpio_pull[paddr[9:2]] = pwdata;
                    10'h003: reg_func_sel[paddr[9:2]]  = pwdata;
                    10'h100: reg_mux_ctrl              = pwdata;
                    10'h101: reg_int_enable            = pwdata;
                    10'h102: reg_int_polarity          = pwdata;
                    default: pslverr = 1'b1;
                endcase
            end else begin
                // 读操作
                case (paddr[11:2])
                    10'h000: prdata = reg_gpio_dir[paddr[9:2]];
                    10'h001: prdata = reg_gpio_out[paddr[9:2]];
                    10'h002: prdata = reg_gpio_pull[paddr[9:2]];
                    10'h003: prdata = reg_func_sel[paddr[9:2]];
                    10'h100: prdata = reg_mux_ctrl;
                    10'h101: prdata = reg_int_enable;
                    10'h102: prdata = reg_int_polarity;
                    10'h103: prdata = reg_int_status;
                    10'h104: prdata = reg_pin_status;
                    default: prdata = 32'h0000_0000;
                endcase
            end
        end
    end
    
    // ============================================================================
    // 引脚复用逻辑
    // ============================================================================
    
    genvar i, j;
    generate
        // GPIO 引脚处理
        for (i = 0; i < 128; i++) begin : GEN_GPIO
            // 方向控制: 1=输出, 0=输入
            assign gpio_oe[i] = reg_gpio_dir[i][0];
            
            // 输出驱动
            assign gpio_o[i] = reg_gpio_out[i][0];
            
            // 输入采样
            always_ff @(posedge clk) begin
                reg_gpio_out[i][0] <= gpio_i[i];
            end
            
            // 引脚驱动
            assign gpio_pin[i] = gpio_oe[i] ? gpio_o[i] : 1'bz;
        end
        
        // I2C 引脚处理
        for (i = 0; i < 8; i++) begin : GEN_I2C
            assign i2c_scl_o[i]  = 1'b0;
            assign i2c_scl_oe[i] = reg_gpio_out[64+i][0];  // GPIO 64-71
            assign i2c_sda_o[i]  = 1'b0;
            assign i2c_sda_oe[i] = reg_gpio_out[72+i][0];  // GPIO 72-79
            
            always_ff @(posedge clk) begin
                reg_gpio_out[64+i][0] <= i2c_scl_i[i];
                reg_gpio_out[72+i][0] <= i2c_sda_i[i];
            end
            
            assign i2c_scl_pin[i] = i2c_scl_oe[i] ? i2c_scl_o[i] : 1'bz;
            assign i2c_sda_pin[i] = i2c_sda_oe[i] ? i2c_sda_o[i] : 1'bz;
        end
        
        // SPI 引脚处理
        for (i = 0; i < 8; i++) begin : GEN_SPI
            assign spi_sclk_o[i]  = reg_gpio_out[80+i][0];   // GPIO 80-87
            assign spi_mosi_o[i]  = reg_gpio_out[88+i][0];   // GPIO 88-95
            assign spi_cs_n_o[i]  = reg_gpio_out[96+i][0];   // GPIO 96-103
            
            always_ff @(posedge clk) begin
                reg_gpio_out[88+i][0] <= spi_miso_i[i];
            end
        end
        
        // UART 引脚处理
        for (i = 0; i < 8; i++) begin : GEN_UART
            assign uart_tx_o[i] = reg_gpio_out[104+i][0];   // GPIO 104-111
            always_ff @(posedge clk) begin
                reg_gpio_out[112+i][0] <= uart_rx_i[i];     // GPIO 112-119
            end
        end
        
        // JTAG 引脚处理
        always_ff @(posedge clk) begin
            reg_gpio_out[120][0] <= jtag_tck_i;
            reg_gpio_out[121][0] <= jtag_tms_i;
            reg_gpio_out[122][0] <= jtag_tdi_i;
            reg_gpio_out[123][0] <= jtag_trst_n_i;
        end
        
        assign jtag_tdo_o = reg_gpio_out[124][0];           // GPIO 124
        
    endgenerate
    
    // ============================================================================
    // 中断状态更新
    // ============================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            reg_int_status <= 32'h0000_0000;
        end else begin
            // 边沿检测中断
            for (int i = 0; i < 128; i++) begin
                if (reg_int_enable[i] && reg_int_polarity[i]) begin
                    if (gpio_i[i] && !reg_int_status[i]) begin
                        reg_int_status[i] <= 1'b1;
                    end
                end
            end
        end
    end
    
    // ============================================================================
    // 启动模式处理
    // ============================================================================
    
    always_comb begin
        // 根据启动模式配置默认引脚功能
        case (boot_mode)
            3'b000: begin  // QSPI Flash 启动
                // SPI0 使用 GPIO 80-87
                reg_func_sel[80] = {28'h0, 4'h3};  // SPI0_SCLK
                reg_func_sel[81] = {28'h0, 4'h3};  // SPI0_MOSI
                reg_func_sel[82] = {28'h0, 4'h3};  // SPI0_MISO
                reg_func_sel[83] = {28'h0, 4'h3};  // SPI0_CS0
            end
            3'b001: begin  // eMMC 启动
                // SDMMC 使用 GPIO 0-15
            end
            3'b010: begin  // NOR Flash 启动
                // NOR 使用 GPIO 80-95
            end
            3'b011: begin  // UART 下载模式
                // UART0 使用 GPIO 104-111
            end
            default: begin
                // 默认使用 GPIO
            end
        endcase
    end
    
endmodule
