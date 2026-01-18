// ============================================================================
// Module: clk_div
// Description: 时钟分频器
// Author: YaoGuang RTL Team
// Version: V1.0
// Date: 2026-03-01
// ============================================================================

`timescale 1ns / 1ps

module clk_div #(
    parameter DIVISOR = 2
) (
    input  logic clk_in,
    input  logic rst_n,
    output logic clk_out
);

    localparam COUNTER_WIDTH = $clog2(DIVISOR);

    // 分频计数器
    logic [COUNTER_WIDTH:0] counter;

    always_ff @(posedge clk_in or negedge rst_n) begin
        if (!rst_n) begin
            counter <= '0;
        end else begin
            if (counter == DIVISOR/2 - 1) begin
                counter <= '0;
            end else begin
                counter <= counter + 1'b1;
            end
        end
    end

    // 输出时钟
    assign clk_out = counter[0];

endmodule
