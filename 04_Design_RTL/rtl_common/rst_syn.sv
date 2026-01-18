// ============================================================================
// Module: rst_syn
// Description: 复位同步器 - 异步复位同步化
// Author: YaoGuang RTL Team
// Version: V1.0
// Date: 2026-03-01
// ============================================================================

`timescale 1ns / 1ps

module rst_syn #(
    parameter SYNC_STAGES = 2,
    parameter RESET_VALUE = 1'b0
) (
    // 异步输入
    input  logic async_rst_n,
    
    // 时钟和输出
    input  logic clk,
    output logic sync_rst_n
);

    // 内部寄存器
    logic [SYNC_STAGES-1:0] sync_chain;

    // 复位同步链
    always_ff @(posedge clk or negedge async_rst_n) begin
        if (!async_rst_n) begin
            sync_chain <= {(SYNC_STAGES){RESET_VALUE}};
        end else begin
            sync_chain <= {sync_chain[SYNC_STAGES-2:0], 1'b1};
        end
    end

    // 输出
    assign sync_rst_n = sync_chain[SYNC_STAGES-1];

endmodule
