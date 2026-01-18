// ============================================================================
// Module: soc_power_domain
// Description: YaoGuang SoC 电源域控制
// Author: YaoGuang RTL Team
// Version: V1.0
// Date: 2026-01-18
// ============================================================================

`timescale 1ns / 1ps

module soc_power_domain (
    // ============================================================================
    // 时钟与复位
    // ============================================================================
    
    input  logic                         clk,
    input  logic                         rst_n,
    
    // ============================================================================
    // 电源域控制输入 (来自 PMU)
    // ============================================================================
    
    input  logic [11:0]                  pwr_on_req,       // 电源域上电请求
    input  logic [11:0]                  pwr_off_req,      // 电源域下电请求
    input  logic [11:0]                  retention_req,    // 保留请求
    
    // ============================================================================
    // 电源域状态输出
    // ============================================================================
    
    output logic [11:0]                  pwr_on_ack,       // 电源域上电确认
    output logic [11:0]                  pwr_off_ack,      // 电源域下电确认
    output logic [11:0]                  retention_ack,    // 保留确认
    output logic [11:0]                  pwr_state,        // 当前电源状态
    output logic [11:0]                  pwr_good,         // 电源良好信号
    output logic [11:0]                  isolation_en,     // 隔离使能
    
    // ============================================================================
    // 电源门控控制输出
    // ============================================================================
    
    output logic [11:0]                  pwr_gate_en,      // 电源门控使能
    output logic [11:0]                  ret_gate_en,      // 保留门控使能
    output logic [11:0]                  iso_p_on,         // 隔离 P 侧
    output logic [11:0]                 iso_n_on,         // 隔离 N 侧
    
    // ============================================================================
    // 状态与状态
    // ============================================================================
    
    output logic                         all_domains_on,   // 所有域上电完成
    output logic                         any_domain_off,   // 任意域下电中
    output logic                         pwr_sequence_err, // 电源序列错误
    output logic [3:0]                   pwr_err_code      // 错误代码
);
    
    // ============================================================================
    // 内部参数
    // ============================================================================
    
    parameter int NUM_PD                 = 12;
    parameter int FSM_WIDTH              = 4;
    parameter logic [FSM_WIDTH-1:0] STATE_OFF         = 4'b0000;
    parameter logic [FSM_WIDTH-1:0] STATE_TURN_ON     = 4'b0001;
    parameter logic [FSM_WIDTH-1:0] STATE_ON          = 4'b0010;
    parameter logic [FSM_WIDTH-1:0] STATE_RETENTION   = 4'b0011;
    parameter logic [FSM_WIDTH-1:0] STATE_TURN_OFF    = 4'b0100;
    parameter logic [FSM_WIDTH-1:0] STATE_ERROR       = 4'b1111;
    
    // 电源域索引定义
    localparam int PD_ALWAYS_ON          = 0;
    localparam int PD_CPU                = 1;
    localparam int PD_SAFETY             = 2;
    localparam int PD_NPU                = 3;
    localparam int PD_GPU                = 4;
    localparam int PD_ISP                = 5;
    localparam int PD_NOC                = 6;
    localparam int PD_MEM                = 7;
    localparam int PD_SYS                = 8;
    localparam int PD_PCIE               = 9;
    localparam int PD_USB                = 10;
    localparam int PD_ETH                = 11;
    
    // ============================================================================
    // 内部信号
    // ============================================================================
    
    logic [NUM_PD-1:0]                   state_q, state_d;
    logic [NUM_PD-1:0]                   turn_on_timer;
    logic [NUM_PD-1:0]                   turn_off_timer;
    logic [NUM_PD-1:0]                   pwr_good_sync;
    logic [NUM_PD-1:0]                   pwr_on_req_sync;
    logic [NUM_PD-1:0]                   pwr_off_req_sync;
    logic [NUM_PD-1:0]                   retention_req_sync;
    logic [NUM_PD-1:0]                   isolation_en_sync;
    
    // ============================================================================
    // 电源状态机 (每个电源域独立)
    // ============================================================================
    
    genvar i;
    generate
        for (i = 0; i < NUM_PD; i++) begin : GEN_PD_FSM
            always_comb begin
                // 默认值
                state_d[i]           = state_q[i];
                pwr_on_ack[i]        = 1'b0;
                pwr_off_ack[i]       = 1'b0;
                retention_ack[i]     = 1'b0;
                pwr_gate_en[i]       = 1'b0;
                ret_gate_en[i]       = 1'b0;
                isolation_en[i]      = 1'b0;
                
                // ALWAYS_ON 域特殊处理
                if (i == PD_ALWAYS_ON) begin
                    state_d[i]           = STATE_ON;
                    pwr_on_ack[i]        = 1'b1;
                    pwr_gate_en[i]       = 1'b1;
                end else begin
                    case (state_q[i])
                        STATE_OFF: begin
                            if (pwr_on_req[i]) begin
                                state_d[i]   = STATE_TURN_ON;
                            end
                        end
                        
                        STATE_TURN_ON: begin
                            // 等待电源稳定
                            if (turn_on_timer[i] == 8'hFF) begin
                                state_d[i]   = STATE_ON;
                                pwr_on_ack[i] = 1'b1;
                                pwr_gate_en[i] = 1'b1;
                            end
                        end
                        
                        STATE_ON: begin
                            pwr_on_ack[i]    = 1'b1;
                            pwr_gate_en[i]   = 1'b1;
                            
                            if (pwr_off_req[i]) begin
                                state_d[i]   = STATE_TURN_OFF;
                            end else if (retention_req[i]) begin
                                state_d[i]   = STATE_RETENTION;
                            end
                        end
                        
                        STATE_RETENTION: begin
                            retention_ack[i] = 1'b1;
                            ret_gate_en[i]   = 1'b1;
                            isolation_en[i]  = 1'b1;
                            
                            if (pwr_off_req[i]) begin
                                state_d[i]   = STATE_TURN_OFF;
                            end else if (!retention_req[i]) begin
                                state_d[i]   = STATE_ON;
                            end
                        end
                        
                        STATE_TURN_OFF: begin
                            pwr_gate_en[i]   = 1'b0;
                            
                            if (turn_off_timer[i] == 8'hFF) begin
                                state_d[i]   = STATE_OFF;
                                pwr_off_ack[i] = 1'b1;
                            end
                        end
                        
                        STATE_ERROR: begin
                            pwr_gate_en[i]   = 1'b0;
                        end
                        
                        default: begin
                            state_d[i]       = STATE_OFF;
                        end
                    endcase
                end
            end
            
            // 状态寄存器
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    state_q[i] <= STATE_OFF;
                end else begin
                    state_q[i] <= state_d[i];
                end
            end
            
            // 定时器逻辑
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    turn_on_timer[i]  <= 8'h00;
                    turn_off_timer[i] <= 8'h00;
                end else begin
                    case (state_q[i])
                        STATE_TURN_ON: begin
                            turn_on_timer[i] <= turn_on_timer[i] + 1;
                        end
                        STATE_TURN_OFF: begin
                            turn_off_timer[i] <= turn_off_timer[i] + 1;
                        end
                        default: begin
                            turn_on_timer[i]  <= 8'h00;
                            turn_off_timer[i] <= 8'h00;
                        end
                    endcase
                end
            end
        end
    endgenerate
    
    // ============================================================================
    // 电源状态输出
    // ============================================================================
    
    always_comb begin
        for (int i = 0; i < NUM_PD; i++) begin
            case (state_q[i])
                STATE_ON:        pwr_state[i] = 2'b00;
                STATE_RETENTION: pwr_state[i] = 2'b01;
                STATE_TURN_ON:   pwr_state[i] = 2'b00;
                STATE_TURN_OFF:  pwr_state[i] = 2'b10;
                STATE_OFF:       pwr_state[i] = 2'b10;
                default:         pwr_state[i] = 2'b10;
            endcase
        end
    end
    
    // ============================================================================
    // 状态汇总
    // ============================================================================
    
    assign all_domains_on = &pwr_on_ack;
    assign any_domain_off = |pwr_off_req;
    
    // 错误检测
    assign pwr_sequence_err = 1'b0;  // 简化的错误检测
    
    // 错误代码
    assign pwr_err_code = 4'b0000;
    
    // ============================================================================
    // 电源良好信号同步
    // ============================================================================
    
    sync_flop #(
        .WIDTH      (NUM_PD),
        .STAGES     (2)
    ) pwr_good_sync_inst (
        .clk        (clk),
        .reset_n    (rst_n),
        .data_in    (pwr_good_sync),
        .data_out   (pwr_good)
    );
    
    // ============================================================================
    // 隔离信号生成
    // ============================================================================
    
    always_comb begin
        iso_p_on  = {NUM_PD{1'b1}};
        iso_n_on  = {NUM_PD{1'b1}};
        
        for (int i = 0; i < NUM_PD; i++) begin
            if (state_q[i] == STATE_RETENTION || state_q[i] == STATE_TURN_OFF) begin
                iso_p_on[i] = 1'b0;
                iso_n_on[i] = 1'b0;
            end
        end
    end
    
endmodule
