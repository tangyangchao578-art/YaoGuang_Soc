// ============================================================================
// Module: soc_glue_logic
// Description: YaoGuang SoC 胶合逻辑
// Author: YaoGuang RTL Team
// Version: V1.0
// Date: 2026-01-18
// ============================================================================

`timescale 1ns / 1ps

module soc_glue_logic (
    // ============================================================================
    // 时钟与复位
    // ============================================================================
    
    input  logic                         clk_sys,          // 系统时钟
    input  logic                         clk_noc,          // NoC 时钟
    input  logic                         rst_sys_n,        // 系统复位
    input  logic                         rst_noc_n,        // NoC 复位
    
    // ============================================================================
    // 中断接口
    // ============================================================================
    
    input  logic                         irq_safety_island, // Safety Island 中断
    input  logic                         irq_npu [4],       // NPU 中断
    input  logic                         irq_gpu,           // GPU 中断
    input  logic                         irq_isp,           // ISP 中断
    input  logic                         irq_display,       // Display 中断
    input  logic                         irq_pcie,          // PCIe 中断
    input  logic                         irq_usb,           // USB 中断
    input  logic                         irq_eth,           // Ethernet 中断
    input  logic                         irq_can [8],       // CAN 中断
    input  logic                         irq_i2c [4],       // I2C 中断
    input  logic                         irq_spi [4],       // SPI 中断
    input  logic                         irq_uart [8],      // UART 中断
    input  logic                         irq_gpio,          // GPIO 中断
    input  logic                         irq_timer,         // 定时器中断
    input  logic                         irq_watchdog,      // 看门狗中断
    input  logic                         irq_rtc,           // RTC 中断
    input  logic                         irq_audio,         // Audio 中断
    input  logic                         irq_crypto,        // Crypto 中断
    input  logic                         irq_ddr,           // DDR 中断
    input  logic                         irq_error,         // 错误中断
    input  logic                         irq_soft,          // 软件中断
    
    output logic                         irq_cpu [8],       // CPU 中断输出
    output logic                         irq_safety_cpu,    // Safety CPU 中断
    
    // ============================================================================
    // AXI 到 APB 桥接
    // ============================================================================
    
    // AXI Master 接口
    input  logic                         m axi_awvalid,
    output logic                         m axi_awready,
    input  logic [31:0]                  m axi_awaddr,
    input  logic [7:0]                   m axi_awlen,
    input  logic [2:0]                   m axi_awsize,
    input  logic [1:0]                   m axi_awburst,
    
    input  logic                         m axi_wvalid,
    output logic                         m axi_wready,
    input  logic [31:0]                  m axi_wdata,
    input  logic [3:0]                   m axi_wstrb,
    input  logic                         m axi_wlast,
    
    output logic                         m axi_bvalid,
    input  logic                         m axi_bready,
    output logic [1:0]                   m axi_bresp,
    
    input  logic                         m axi_arvalid,
    output logic                         m axi_arready,
    input  logic [31:0]                  m axi_araddr,
    input  logic [7:0]                   m axi_arlen,
    input  logic [2:0]                   m axi_arsize,
    input  logic [1:0]                   m axi_arburst,
    
    output logic                         m axi_rvalid,
    input  logic                         m axi_rready,
    output logic [31:0]                  m axi_rdata,
    output logic [1:0]                   m axi_rresp,
    output logic                         m axi_rlast,
    
    // APB Slave 接口
    output logic                         s apb_paddr,
    output logic                         s apb_psel,
    output logic                         s apb_penable,
    output logic                         s apb_pwrite,
    output logic [31:0]                  s apb_pwdata,
    input  logic [31:0]                  s apb_prdata,
    input  logic                         s apb_pslverr,
    input  logic                         s apb_pready,
    
    // ============================================================================
    // 错误报告
    // ============================================================================
    
    input  logic                         err_addr_decode,   // 地址解码错误
    input  logic                         err_timeout,       // 超时错误
    input  logic                         err_access,        // 访问错误
    input  logic                         err_security,      // 安全错误
    
    output logic                         soc_error,         // SoC 错误状态
    output logic [3:0]                   err_code,          // 错误代码
    
    // ============================================================================
    // 状态信号
    // ============================================================================
    
    input  logic                         init_done,         // 初始化完成
    input  logic                         pll_lock,          // PLL 锁定
    input  logic [11:0]                  pwr_domain_on,     // 电源域状态
    
    output logic                         boot_done,         // 启动完成
    output logic                         system_ready       // 系统就绪
);
    
    // ============================================================================
    // 内部信号
    // ============================================================================
    
    logic                                axi_to_apb_awvalid;
    logic                                axi_to_apb_awready;
    logic [31:0]                         axi_to_apb_awaddr;
    logic                                axi_to_apb_wvalid;
    logic                                axi_to_apb_wready;
    logic [31:0]                         axi_to_apb_wdata;
    logic                                axi_to_apb_wlast;
    logic                                axi_to_apb_bvalid;
    logic                                axi_to_apb_bready;
    logic [1:0]                          axi_to_apb_bresp;
    logic                                axi_to_apb_arvalid;
    logic                                axi_to_apb_arready;
    logic [31:0]                         axi_to_apb_araddr;
    logic                                axi_to_apb_rvalid;
    logic                                axi_to_apb_rready;
    logic [31:0]                         axi_to_apb_rdata;
    logic [1:0]                          axi_to_apb_rresp;
    logic                                axi_to_apb_rlast;
    
    logic                                boot_counter_enable;
    logic [15:0]                         boot_counter;
    
    // ============================================================================
    // AXI 到 APB 桥接实例化
    // ============================================================================
    
    apb4_to_ax i_axip_bridge (
        .clk              (clk_sys),
        .rst_n            (rst_sys_n),
        
        // AXI4 Master 接口
        .s_awvalid        (m axi_awvalid),
        .s_awready        (m axi_awready),
        .s_awaddr         (m axi_awaddr),
        .s_awlen          (m axi_awlen),
        .s_awsize         (m axi_awsize),
        .s_awburst        (m axi_awburst),
        
        .s_wvalid         (m axi_wvalid),
        .s_wready         (m axi_wready),
        .s_wdata          (m axi_wdata),
        .s_wstrb          (m axi_wstrb),
        .s_wlast          (m axi_wlast),
        
        .s_bvalid         (m axi_bvalid),
        .s_bready         (m axi_bready),
        .s_bresp          (m axi_bresp),
        
        .s_arvalid        (m axi_arvalid),
        .s_arready        (m axi_arready),
        .s_araddr         (m axi_araddr),
        .s_arlen          (m axi_arlen),
        .s_arsize         (m axi_arsize),
        .s_arburst        (m axi_arburst),
        
        .s_rvalid         (m axi_rvalid),
        .s_rready         (m axi_rready),
        .s_rdata          (m axi_rdata),
        .s_rresp          (m axi_rresp),
        .s_rlast          (m axi_rlast),
        
        // APB4 Slave 接口
        .m_paddr          (s apb_paddr),
        .m_psel           (s apb_psel),
        .m_penable        (s apb_penable),
        .m_pwrite         (s apb_pwrite),
        .m_pwdata         (s apb_pwdata),
        .m_prdata         (s apb_prdata),
        .m_pslverr        (s apb_pslverr),
        .m_pready         (s apb_pready)
    );
    
    // ============================================================================
    // 中断聚合逻辑
    // ============================================================================
    
    // Safety Island 中断路由到 Safety CPU
    assign irq_safety_cpu = irq_safety_island;
    
    // CPU 中断路由 (简化版 - 所有中断路由到所有 CPU)
    // 实际实现中应该使用 GIC 进行中断分发
    genvar i;
    generate
        for (i = 0; i < 8; i++) begin : GEN_CPU_IRQ
            assign irq_cpu[i] = irq_npu[0] | irq_npu[1] | irq_npu[2] | irq_npu[3] |
                               irq_gpu | irq_isp | irq_display | irq_pcie |
                               irq_usb | irq_eth | irq_can[0] | irq_can[1] |
                               irq_i2c[0] | irq_spi[0] | irq_uart[0] | irq_gpio |
                               irq_timer | irq_watchdog | irq_rtc | irq_audio |
                               irq_crypto | irq_ddr | irq_error | irq_soft;
        end
    endgenerate
    
    // ============================================================================
    // 错误处理逻辑
    // ============================================================================
    
    always_comb begin
        soc_error = 1'b0;
        err_code  = 4'b0000;
        
        if (err_addr_decode) begin
            soc_error = 1'b1;
            err_code  = 4'b0001;
        end else if (err_timeout) begin
            soc_error = 1'b1;
            err_code  = 4'b0010;
        end else if (err_access) begin
            soc_error = 1'b1;
            err_code  = 4'b0101;
        end else if (err_security) begin
            soc_error = 1'b1;
            err_code  = 4'b0110;
        end
    end
    
    // ============================================================================
    // 启动完成逻辑
    // ============================================================================
    
    always_ff @(posedge clk_sys or negedge rst_sys_n) begin
        if (!rst_sys_n) begin
            boot_counter     <= 16'h0000;
            boot_counter_enable <= 1'b0;
            boot_done        <= 1'b0;
            system_ready     <= 1'b0;
        end else begin
            if (init_done && pll_lock) begin
                boot_counter_enable <= 1'b1;
            end
            
            if (boot_counter_enable) begin
                boot_counter <= boot_counter + 1;
                
                // 等待 100us 后设置启动完成
                if (boot_counter == 16'h186A) begin  // 100us @ 1MHz
                    boot_done    <= 1'b1;
                end
                
                // 等待 1ms 后设置系统就绪
                if (boot_counter == 16'h0F424) begin  // 1ms @ 1MHz
                    system_ready <= 1'b1;
                end
            end
        end
    end
    
endmodule
