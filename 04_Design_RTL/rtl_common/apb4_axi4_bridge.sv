// ============================================================================
// Module: apb4_axi4_bridge
// Description: APB4 到 AXI4 桥接器
// Author: YaoGuang RTL Team
// Version: V1.0
// Date: 2026-03-01
// ============================================================================

`timescale 1ns / 1ps

module apb4_axi4_bridge #(
    parameter AXI_DATA_WIDTH = 64,
    parameter AXI_ADDR_WIDTH = 32,
    parameter APB_DATA_WIDTH = 32,
    parameter APB_ADDR_WIDTH = 16
) (
    // 时钟复位
    input  logic clk,
    input  logic rst_n,
    
    // AXI4 Slave 接口 (从系统 NoC 视角)
    output logic                         s_arready,
    input  logic                         s_arvalid,
    input  logic [AXI_ADDR_WIDTH-1:0]     s_araddr,
    input  logic [7:0]                   s_arlen,
    input  logic [2:0]                   s_arsize,
    input  logic [1:0]                   s_arburst,
    
    output logic                         s_rready,
    output logic                         s_rvalid,
    output logic [AXI_DATA_WIDTH-1:0]     s_rdata,
    output logic [1:0]                   s_rresp,
    output logic                         s_rlast,
    
    output logic                         s_awready,
    input  logic                         s_awvalid,
    input  logic [AXI_ADDR_WIDTH-1:0]     s_awaddr,
    input  logic [7:0]                   s_awlen,
    input  logic [2:0]                   s_awsize,
    input  logic [1:0]                   s_awburst,
    
    output logic                         s_wready,
    input  logic                         s_wvalid,
    input  logic [AXI_DATA_WIDTH-1:0]     s_wdata,
    input  logic [(AXI_DATA_WIDTH/8)-1:0] s_wstrb,
    input  logic                         s_wlast,
    
    output logic                         s_bready,
    output logic                         s_bvalid,
    output logic [1:0]                   s_bresp,
    
    // APB4 Master 接口 (到外设)
    output logic [APB_ADDR_WIDTH-1:0]    paddr,
    output logic [APB_DATA_WIDTH-1:0]    pwdata,
    input  logic [APB_DATA_WIDTH-1:0]    prdata,
    output logic                         pwrite,
    output logic                         psel,
    output logic                         penable,
    input  logic                         pready,
    output logic [3:0]                   pstrb
);

    // 内部参数
    localparam AXI2APB_RATIO = AXI_DATA_WIDTH / APB_DATA_WIDTH;
    localparam BEAT_WIDTH = $clog2(AXI2APB_RATIO);
    localparam TRANSFER_WIDTH = $clog2(2**8); // Max burst length 256

    // AXI 读状态机
    typedef enum logic [1:0] {
        AR_IDLE,
        AR_ACTIVE,
        AR_DATA,
        AR_RESP
    } ar_state_t;

    ar_state_t ar_state, ar_next_state;
    logic [7:0] ar_len_cnt;
    logic [BEAT_WIDTH-1:0] ar_beat_cnt;
    
    // AXI 写状态机
    typedef enum logic [1:0] {
        AW_IDLE,
        AW_ACTIVE,
        W_ACTIVE,
        B_RESP
    } aw_state_t;

    aw_state_t aw_state, aw_next_state;
    logic [7:0] aw_len_cnt;
    logic [BEAT_WIDTH-1:0] aw_beat_cnt;
    
    // 数据暂存
    logic [AXI_DATA_WIDTH-1:0] rdata_reg;
    logic [AXI_DATA_WIDTH-1:0] wdata_reg;
    logic [(AXI_DATA_WIDTH/8)-1:0] wstrb_reg;
    logic [AXI_ADDR_WIDTH-1:0] awaddr_reg;
    
    // APB 转换信号
    logic apb_transfer;
    logic [AXI_ADDR_WIDTH-1:0] apb_addr;
    logic [AXI_DATA_WIDTH-1:0] apb_wdata;
    logic [AXI_DATA_WIDTH-1:0] apb_rdata;
    logic apb_write;
    
    // APB 选通信号
    logic [AXI2APB_RATIO-1:0] apb_sel;
    logic apb_psel, apb_penable;
    
    // ============================================================================
    // AXI 读通道状态机
    // ============================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ar_state <= AR_IDLE;
            ar_len_cnt <= '0;
            ar_beat_cnt <= '0;
        end else begin
            ar_state <= ar_next_state;
            if (ar_state == AR_IDLE && s_arvalid && s_arready) begin
                ar_len_cnt <= s_arlen;
                ar_beat_cnt <= '0;
            end else if (ar_state == AR_DATA && s_rready && s_rvalid) begin
                if (ar_beat_cnt == AXI2APB_RATIO - 1) begin
                    ar_len_cnt <= ar_len_cnt - 1'b1;
                    ar_beat_cnt <= '0;
                end else begin
                    ar_beat_cnt <= ar_beat_cnt + 1'b1;
                end
            end
        end
    end
    
    always_comb begin
        ar_next_state = ar_state;
        s_arready = 1'b0;
        s_rvalid = 1'b0;
        s_rlast = 1'b0;
        
        case (ar_state)
            AR_IDLE: begin
                s_arready = 1'b1;
                if (s_arvalid) begin
                    ar_next_state = AR_ACTIVE;
                end
            end
            
            AR_ACTIVE: begin
                ar_next_state = AR_DATA;
            end
            
            AR_DATA: begin
                s_rvalid = 1'b1;
                if (s_rready) begin
                    if (ar_beat_cnt == AXI2APB_RATIO - 1) begin
                        if (ar_len_cnt == 8'h00) begin
                            s_rlast = 1'b1;
                            ar_next_state = AR_RESP;
                        end else begin
                            ar_next_state = AR_DATA;
                        end
                    end
                end
            end
            
            AR_RESP: begin
                ar_next_state = AR_IDLE;
            end
            
            default: begin
                ar_next_state = AR_IDLE;
            end
        endcase
    end
    
    // APB 读地址
    assign apb_addr = (ar_state == AR_ACTIVE) ? s_araddr : '0;
    assign apb_write = 1'b0; // 读操作
    
    // APB 读数据暂存
    assign s_rdata = rdata_reg;
    assign s_rresp = 2'b00; // OKAY response
    
    // ============================================================================
    // AXI 写通道状态机
    // ============================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            aw_state <= AW_IDLE;
            aw_len_cnt <= '0;
            aw_beat_cnt <= '0;
            awaddr_reg <= '0;
            wdata_reg <= '0;
            wstrb_reg <= '0;
        end else begin
            aw_state <= aw_next_state;
            if (aw_state == AW_IDLE && s_awvalid && s_awready) begin
                aw_len_cnt <= s_awlen;
                aw_beat_cnt <= '0;
                awaddr_reg <= s_awaddr;
            end else if (aw_state == W_ACTIVE && s_wvalid && s_wready) begin
                if (aw_beat_cnt == AXI2APB_RATIO - 1) begin
                    aw_len_cnt <= aw_len_cnt - 1'b1;
                    aw_beat_cnt <= '0;
                end else begin
                    aw_beat_cnt <= aw_beat_cnt + 1'b1;
                    wdata_reg <= s_wdata;
                    wstrb_reg <= s_wstrb;
                end
            end
        end
    end
    
    always_comb begin
        aw_next_state = aw_state;
        s_awready = 1'b0;
        s_wready = 1'b0;
        s_bvalid = 1'b0;
        s_bresp = 2'b00;
        
        case (aw_state)
            AW_IDLE: begin
                s_awready = 1'b1;
                if (s_awvalid) begin
                    aw_next_state = AW_ACTIVE;
                end
            end
            
            AW_ACTIVE: begin
                aw_next_state = W_ACTIVE;
            end
            
            W_ACTIVE: begin
                s_wready = 1'b1;
                if (s_wvalid && s_wready) begin
                    if (aw_beat_cnt == AXI2APB_RATIO - 1) begin
                        if (aw_len_cnt == 8'h00) begin
                            aw_next_state = B_RESP;
                        end else begin
                            aw_next_state = W_ACTIVE;
                        end
                    end
                end
            end
            
            B_RESP: begin
                s_bvalid = 1'b1;
                if (s_bready) begin
                    aw_next_state = AW_IDLE;
                end
            end
            
            default: begin
                aw_next_state = AW_IDLE;
            end
        endcase
    end
    
    // APB 写地址
    assign apb_addr = (aw_state == AW_ACTIVE) ? s_awaddr : awaddr_reg;
    assign apb_wdata = (aw_state == W_ACTIVE) ? s_wdata : wdata_reg;
    assign apb_write = 1'b1;
    
    // ============================================================================
    // APB 信号生成
    // ============================================================================
    
    // APB 选通信号
    assign apb_psel = (ar_state == AR_DATA) || (aw_state == W_ACTIVE);
    assign apb_penable = apb_psel;
    
    // APB 地址输出
    assign paddr = apb_addr[APB_ADDR_WIDTH-1:0];
    
    // APB 写数据输出
    assign pwdata = (apb_write) ? apb_wdata[APB_DATA_WIDTH-1:0] : '0;
    
    // APB 写使能输出
    assign pwrite = apb_write;
    
    // APB 选通使能输出
    assign psel = apb_psel;
    assign penable = apb_penable;
    
    // APB 写字节使能输出
    assign pstrb = (apb_write) ? apb_wdata[(APB_DATA_WIDTH/8)*4-1:(APB_DATA_WIDTH/8)*4] : 4'b1111;
    
    // APB 读数据输入
    assign apb_rdata = {{(AXI_DATA_WIDTH-APB_DATA_WIDTH){1'b0}}, prdata};
    
    // 读数据暂存
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rdata_reg <= '0;
        end else if (ar_state == AR_DATA && pready) begin
            rdata_reg <= apb_rdata;
        end
    end

endmodule
