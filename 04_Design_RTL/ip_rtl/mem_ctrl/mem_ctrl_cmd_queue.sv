//-----------------------------------------------------------------------------
// LPDDR5 Memory Controller Command Queue
// YaoGuang SoC Project
//-----------------------------------------------------------------------------
// Description:
//   Synchronous FIFO for command queue management
//   Supports 64-entry depth as per architecture spec
//-----------------------------------------------------------------------------
// Version: 1.0
// Date: 2026-01-18
//-----------------------------------------------------------------------------

`timescale 1ps/1fs

module mem_ctrl_cmd_queue #(
    parameter WIDTH     = 72,    // ID + ADDR + control
    parameter DEPTH     = 64,
    parameter TCQ       = 100
) (
    // ----------------------
    // Clock and Reset
    // ----------------------
    input  wire             clk_i,
    input  wire             rst_n_i,

    // ----------------------
    // Write Interface
    // ----------------------
    input  wire             wr_en_i,
    input  wire [WIDTH-1:0] wr_data_i,
    output wire             full_o,

    // ----------------------
    // Read Interface
    // ----------------------
    input  wire             rd_en_i,
    output wire [WIDTH-1:0] rd_data_o,
    output wire             empty_o
);

    // ----------------------
    // Parameters
    // ----------------------
    localparam ADDR_WIDTH = $clog2(DEPTH);

    // ----------------------
    // Signals
    // ----------------------
    reg  [WIDTH-1:0]        mem_r [0:DEPTH-1];
    reg  [ADDR_WIDTH:0]     wr_ptr_r;
    reg  [ADDR_WIDTH:0]     rd_ptr_r;
    reg                     full_r;
    reg                     empty_r;

    wire [ADDR_WIDTH:0]     wr_ptr_next;
    wire [ADDR_WIDTH:0]     rd_ptr_next;
    wire                    full_next;
    wire                    empty_next;

    // ----------------------
    // Assigns
    // ----------------------
    assign full_o  = full_r;
    assign empty_o = empty_r;
    assign rd_data_o = mem_r[rd_ptr_r[ADDR_WIDTH-1:0]];

    // ----------------------
    // Write Pointer
    // ----------------------
    assign wr_ptr_next = wr_ptr_r + 1'b1;
    assign full_next = (wr_ptr_next == rd_ptr_r) ||
                       ((wr_ptr_next[ADDR_WIDTH] != rd_ptr_r[ADDR_WIDTH]) &&
                        (wr_ptr_next[ADDR_WIDTH-1:0] == rd_ptr_r[ADDR_WIDTH-1:0]));

    always @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            wr_ptr_r <= '0;
            full_r <= 1'b0;
        end else begin
            if (wr_en_i && !full_r) begin
                mem_r[wr_ptr_r[ADDR_WIDTH-1:0]] <= wr_data_i;
                wr_ptr_r <= wr_ptr_next;
                full_r <= full_next;
            end
        end
    end

    // ----------------------
    // Read Pointer
    // ----------------------
    assign rd_ptr_next = rd_ptr_r + 1'b1;
    assign empty_next = (rd_ptr_next == wr_ptr_r);

    always @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            rd_ptr_r <= '0;
            empty_r <= 1'b1;
        end else begin
            if (rd_en_i && !empty_r) begin
                rd_ptr_r <= rd_ptr_next;
                empty_r <= empty_next;
            end
        end
    end

endmodule
