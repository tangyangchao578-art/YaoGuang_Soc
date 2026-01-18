// ============================================================================
// Module: boot_rom_wrapper
// Description: YaoGuang SoC Boot ROM 封装
// Author: YaoGuang RTL Team
// Version: V1.0
// Date: 2026-01-18
// ============================================================================

`timescale 1ns / 1ps

module boot_rom_wrapper (
    // ============================================================================
    // 时钟与复位
    // ============================================================================
    
    input  logic                         clk,
    input  logic                         rst_n,
    
    // ============================================================================
    // AXI4 Slave 接口
    // ============================================================================
    
    input  logic                         s_awvalid,
    output logic                         s_awready,
    input  logic [31:0]                  s_awaddr,
    input  logic [7:0]                   s_awlen,
    input  logic [2:0]                   s_awsize,
    input  logic [1:0]                   s_awburst,
    input  logic [3:0]                   s_awqos,
    input  logic [3:0]                   s_awprot,
    
    input  logic                         s_wvalid,
    output logic                         s_wready,
    input  logic [63:0]                  s_wdata,
    input  logic [7:0]                   s_wstrb,
    input  logic                         s_wlast,
    
    output logic                         s_bvalid,
    input  logic                         s_bready,
    output logic [1:0]                   s_bresp,
    
    input  logic                         s_arvalid,
    output logic                         s_arready,
    input  logic [31:0]                  s_araddr,
    input  logic [7:0]                   s_arlen,
    input  logic [2:0]                   s_arsize,
    input  logic [1:0]                   s_arburst,
    input  logic [3:0]                   s_arqos,
    input  logic [3:0]                   s_arprot,
    
    output logic                         s_rvalid,
    input  logic                         s_rready,
    output logic [63:0]                  s_rdata,
    output logic [1:0]                   s_rresp,
    output logic                         s_rlast,
    
    // ============================================================================
    // 状态信号
    // ============================================================================
    
    output logic                         boot_error,
    input  logic                         secure_boot_en,    // 安全启动使能
    output logic [31:0]                  boot_rom_hash      // Boot ROM 哈希
);
    
    // ============================================================================
    // 参数定义
    // ============================================================================
    
    parameter int ROM_SIZE               = 256 * 1024;      // 256 KB
    parameter int ADDR_WIDTH             = 18;              // 2^18 = 256KB
    parameter int DATA_WIDTH             = 64;
    parameter int NUM_WORDS              = ROM_SIZE / 8;    // 64-bit words
    
    // ============================================================================
    // 内部信号
    // ============================================================================
    
    logic [ADDR_WIDTH-1:0]               read_addr;
    logic                                rom_cs;
    logic                                rom_oe;
    logic [DATA_WIDTH-1:0]               rom_data;
    logic                                axi_arvalid_q;
    logic [31:0]                         s_araddr_q;
    logic                                axi_awvalid_q;
    logic [31:0]                         s_awaddr_q;
    
    // ============================================================================
    // Boot ROM 存储器实例化
    // ============================================================================
    
    // ROM 地址解码
    assign rom_cs = 1'b1;  // 始终使能 (只读)
    assign rom_oe = s_arvalid & s_arready;
    assign read_addr = s_araddr[ADDR_WIDTH-1:3];
    
    // Boot ROM 存储器 (初始化文件)
    boot_rom #(
        .SIZE           (NUM_WORDS),
        .ADDR_WIDTH     (ADDR_WIDTH),
        .DATA_WIDTH     (DATA_WIDTH),
        .INIT_FILE      ("boot_rom.mem")
    ) boot_rom_inst (
        .clk            (clk),
        .cs             (rom_cs),
        .oe             (rom_oe),
        .addr           (read_addr),
        .data           (rom_data)
    );
    
    // ============================================================================
    // AXI4 读通道处理
    // ============================================================================
    
    assign s_arready = s_rvalid ? s_rready : 1'b1;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            s_rvalid   <= 1'b0;
            s_rdata    <= 64'h0000_0000_0000_0000;
            s_rresp    <= 2'b00;
            s_rlast    <= 1'b1;
            s_araddr_q <= 32'h0000_0000;
        end else begin
            if (s_arvalid && s_arready) begin
                s_araddr_q <= s_araddr;
            end
            
            if (s_rvalid && s_rready) begin
                s_rvalid <= 1'b0;
            end else if (s_arvalid && s_arready) begin
                s_rvalid <= 1'b1;
                s_rdata  <= rom_data;
                s_rresp  <= 2'b00;
                s_rlast  <= 1'b1;
            end
        end
    end
    
    // ============================================================================
    // AXI4 写通道处理 (Boot ROM 只读, 返回错误)
    // ============================================================================
    
    assign s_awready = 1'b0;  // 不接受写请求
    assign s_wready  = 1'b0;  // 不接受写请求
    assign s_bvalid  = s_awvalid & s_awready;
    assign s_bresp   = 2'b11;  // SLVERR
    
    // ============================================================================
    // 安全启动验证
    // ============================================================================
    
    // Boot ROM 哈希计算 (简化版)
    sha256 #(
        .DATA_WIDTH     (64),
        .BLOCK_SIZE     (64)
    ) boot_rom_sha (
        .clk            (clk),
        .rst_n          (rst_n),
        .data_in        (rom_data),
        .data_valid     (s_rvalid),
        .hash_out       (boot_rom_hash),
        .hash_valid     ()
    );
    
    // Boot 错误检测
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            boot_error <= 1'b0;
        end else begin
            // 检测到写访问时设置错误
            if (s_awvalid) begin
                boot_error <= 1'b1;
            end
        end
    end
    
endmodule
