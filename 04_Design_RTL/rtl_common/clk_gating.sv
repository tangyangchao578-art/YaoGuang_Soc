// ============================================================================
// Module: clk_gating
// Description: 时钟门控单元
// Author: YaoGuang RTL Team
// Version: V1.0
// Date: 2026-03-01
// ============================================================================

`timescale 1ns / 1ps

module clk_gating #(
    parameter NUM_PORTS = 8
) (
    input  logic clk_in,
    input  logic clk_en,
    input  logic test_mode,
    output logic clk_out
);

    // 时钟门控实现
    assign clk_out = (clk_en || test_mode) ? clk_in : 1'b0;

endmodule
