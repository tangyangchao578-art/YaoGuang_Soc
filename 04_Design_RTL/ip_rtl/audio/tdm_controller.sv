// Copyright (c) 2026 YaoGuang SoC Project
// All rights reserved

// TDM Controller Module
// Revision: 1.0
// Date: 2026-01-18

`timescale 1ns/1ps

module tdm_controller #(
    parameter CHANNEL_NUM = 8,
    parameter SLOT_WIDTH  = 16
) (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         enable,

    // External TDM Interface
    input  wire         bclk_i,
    output wire         bclk_o,
    inout  wire         bclk_t,
    input  wire         fs_i,
    output wire         fs_o,
    inout  wire         fs_t,
    output wire [SLOT_WIDTH-1:0] dout,
    input  wire [SLOT_WIDTH-1:0] din,

    // PCM Data Interface
    output wire [31:0]  pcm_dout,
    output wire         pcm_dout_valid,
    input  wire [31:0]  pcm_din,
    input  wire         pcm_din_valid
);

    // Parameters
    localparam FRAME_SIZE = CHANNEL_NUM * SLOT_WIDTH;

    // Control Register
    reg  [7:0]   ctrl_reg;
    wire [7:0]   stat_reg;

    // Internal Signals
    reg          master_mode;
    reg  [7:0]   bit_cnt;
    reg  [4:0]   slot_cnt;
    reg          fs_reg;
    reg          prev_fs;
    reg          fs_edge;
    reg  [SLOT_WIDTH-1:0]  tx_shift_reg;
    reg  [SLOT_WIDTH-1:0]  rx_shift_reg;
    reg          tx_empty;
    reg          rx_full;
    reg          bclk_sync;
    reg          fs_sync;
    reg          bclk_d;
    reg          fs_d;

    // State Machine
    localparam IDLE  = 2'b00;
    localparam TRANSFER = 2'b01;

    reg [1:0]   state;

    // I/O
    assign bclk_o   = master_mode ? bclk_reg : 1'b0;
    assign bclk_t   = master_mode ? 1'b0 : 1'bz;
    assign fs_o     = master_mode ? fs_reg : 1'b0;
    assign fs_t     = master_mode ? 1'b0 : 1'bz;

    // BCLK generation (master mode)
    reg bclk_reg;
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            bclk_reg <= 1'b0;
        end else if (master_mode && enable) begin
            bclk_reg <= ~bclk_reg;
        end else begin
            bclk_reg <= 1'b0;
        end
    end

    // FS (Frame Sync) generation
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            fs_reg <= 1'b0;
        end else if (enable && master_mode) begin
            if (fs_edge) begin
                fs_reg <= 1'b1;
            end else if (bit_cnt == SLOT_WIDTH - 1) begin
                fs_reg <= 1'b0;
            end
        end
    end

    // Synchronize external signals (slave mode)
    always @(posedge clk) begin
        bclk_d     <= bclk_i;
        bclk_sync  <= bclk_d;
        fs_d       <= fs_i;
        fs_sync    <= fs_d;
    end

    // Frame sync edge detection
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            prev_fs <= 1'b0;
            fs_edge <= 1'b0;
        end else begin
            fs_edge <= fs_sync && !prev_fs;
            prev_fs <= fs_sync;
        end
    end

    // Bit counter
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            bit_cnt <= 8'd0;
        end else if (!enable) begin
            bit_cnt <= 8'd0;
        end else begin
            if (master_mode) begin
                if (bit_cnt == SLOT_WIDTH - 1) begin
                    bit_cnt <= 8'd0;
                end else begin
                    bit_cnt <= bit_cnt + 1'b1;
                end
            end else begin
                if (bclk_sync && !bclk_d) begin
                    if (bit_cnt == SLOT_WIDTH - 1) begin
                        bit_cnt <= 8'd0;
                    end else begin
                        bit_cnt <= bit_cnt + 1'b1;
                    end
                end
            end
        end
    end

    // Slot counter
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            slot_cnt <= 5'd0;
        end else if (!enable) begin
            slot_cnt <= 5'd0;
        end else begin
            if (bit_cnt == SLOT_WIDTH - 1) begin
                if (slot_cnt == CHANNEL_NUM - 1) begin
                    slot_cnt <= 5'd0;
                end else begin
                    slot_cnt <= slot_cnt + 1'b1;
                end
            end
        end
    end

    // TX Shift Register
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            tx_shift_reg <= {SLOT_WIDTH{1'b0}};
            tx_empty     <= 1'b1;
        end else if (!enable) begin
            tx_shift_reg <= {SLOT_WIDTH{1'b0}};
            tx_empty     <= 1'b1;
        end else begin
            if (pcm_din_valid && tx_empty && bit_cnt == SLOT_WIDTH - 1) begin
                tx_shift_reg <= pcm_din[SLOT_WIDTH-1:0];
                tx_empty     <= 1'b0;
            end else if ((master_mode ? 1'b1 : bclk_sync) && !bclk_d) begin
                if (bit_cnt < SLOT_WIDTH - 1) begin
                    tx_shift_reg <= {tx_shift_reg[SLOT_WIDTH-2:0], 1'b0};
                end else begin
                    if (!tx_empty) begin
                        tx_empty <= 1'b1;
                    end
                end
            end
        end
    end

    // TX Data Output
    assign dout = tx_shift_reg[SLOT_WIDTH-1];

    // RX Shift Register
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rx_shift_reg <= {SLOT_WIDTH{1'b0}};
            rx_full      <= 1'b0;
        end else if (!enable) begin
            rx_shift_reg <= {SLOT_WIDTH{1'b0}};
            rx_full      <= 1'b0;
        end else begin
            if ((master_mode ? 1'b1 : bclk_sync) && !bclk_d) begin
                rx_shift_reg <= {rx_shift_reg[SLOT_WIDTH-2:0], din};
                if (bit_cnt == SLOT_WIDTH - 1) begin
                    rx_full <= 1'b1;
                end
            end else if (pcm_dout_valid) begin
                rx_full <= 1'b0;
            end
        end
    end

    // RX Data Output
    assign pcm_dout       = {{32-SLOT_WIDTH{rx_shift_reg[SLOT_WIDTH-1]}}, rx_shift_reg};
    assign pcm_dout_valid = rx_full;

    // Control Register
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ctrl_reg <= 8'd0;
        end else begin
            if (pwrite && psel && penable) begin
                if (paddr == 8'h18) begin
                    ctrl_reg <= pwdata[7:0];
                end
            end
        end
    end

    // Master mode
    assign master_mode = ctrl_reg[0];

    // Status Register
    assign stat_reg = {7'd0, rx_full};

endmodule
