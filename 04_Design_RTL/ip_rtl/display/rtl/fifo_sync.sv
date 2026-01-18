// -----------------------------------------------------------------------------
// File: fifo_sync.sv
// Description: Synchronous FIFO with optional parity
// Author: YaoGuang SoC Design Team
// Date: 2026-01-18
// -----------------------------------------------------------------------------

`timescale 1ns/1ps

module fifo_sync #(
    parameter integer WIDTH = 64,
    parameter integer DEPTH = 16
) (
    input  logic                                    clk,
    input  logic                                    rst_n,
    input  logic                                    wr_en,
    input  logic [WIDTH-1:0]                        wr_data,
    output logic                                    full,
    input  logic                                    rd_en,
    output logic [WIDTH-1:0]                        rd_data,
    output logic                                    empty,
    output logic [$clog2(DEPTH):0]                  count
);

    localparam integer ADDR_WIDTH = $clog2(DEPTH);

    logic [WIDTH-1:0]                               mem [0:DEPTH-1];
    logic [ADDR_WIDTH-1:0]                          wr_ptr, rd_ptr;
    logic [ADDR_WIDTH:0]                            ptr_diff;

    // Write Pointer
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_ptr <= '0;
        end else begin
            if (wr_en && !full) begin
                wr_ptr <= wr_ptr + 1'd1;
                mem[wr_ptr] <= wr_data;
            end
        end
    end

    // Read Pointer
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_ptr <= '0;
        end else begin
            if (rd_en && !empty) begin
                rd_ptr <= rd_ptr + 1'd1;
            end
        end
    end

    // Status Signals
    assign ptr_diff = wr_ptr - rd_ptr;
    assign full  = (ptr_diff[ADDR_WIDTH] == 1'b1);
    assign empty = (ptr_diff == '0);
    assign count = ptr_diff[ADDR_WIDTH:0];
    assign rd_data = mem[rd_ptr];

endmodule
