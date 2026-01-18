// -----------------------------------------------------------------------------
// File: display_clk_rst.sv
// Description: Display Subsystem Clock and Reset Management
// Author: YaoGuang SoC Design Team
// Date: 2026-01-18
// -----------------------------------------------------------------------------

`timescale 1ns/1ps

module display_clk_rst (
    input  logic                                    clk_sys,
    input  logic                                    rst_n,
    output logic                                    pixel_clk,
    output logic                                    rst_pixel_n,
    output logic                                    clk_locked
);

    logic [1:0]                                     clk_div;
    logic [3:0]                                     rst_sync;
    logic                                           pixel_clk_int;

    // Clock Divider (for simulation - in real design use PLL)
    always_ff @(posedge clk_sys or negedge rst_n) begin
        if (!rst_n) begin
            clk_div <= 2'd0;
        end else begin
            clk_div <= clk_div + 2'd1;
        end
    end

    assign pixel_clk_int = clk_div[1];

    // Reset Synchronizer
    always_ff @(posedge pixel_clk_int or negedge rst_n) begin
        if (!rst_n) begin
            rst_sync <= 4'd0;
        end else begin
            rst_sync <= {rst_sync[2:0], rst_n};
        end
    end

    assign rst_pixel_n = rst_sync[3];
    assign pixel_clk = pixel_clk_int;
    assign clk_locked = rst_n;

endmodule
