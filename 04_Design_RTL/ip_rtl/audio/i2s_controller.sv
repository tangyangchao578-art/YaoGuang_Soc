// Copyright (c) 2026 YaoGuang SoC Project
// All rights reserved

// I2S Controller Module
// Revision: 1.0
// Date: 2026-01-18

`timescale 1ns/1ps

module i2s_controller #(
    parameter CHANNEL_NUM = 2
) (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         enable,

    // External I2S Interface
    input  wire         bclk_i,
    output wire         bclk_o,
    inout  wire         bclk_t,
    input  wire         lrclk_i,
    output wire         lrclk_o,
    inout  wire         lrclk_t,
    output wire         dout,
    input  wire         din,
    output wire         mclk,

    // PCM Data Interface
    output wire [31:0]  pcm_dout,
    output wire         pcm_dout_valid,
    input  wire [31:0]  pcm_din,
    input  wire         pcm_din_valid
);

    // Parameters
    localparam DATA_WIDTH = 32;

    // Control Register
    reg  [7:0]   ctrl_reg;
    wire [7:0]   stat_reg;

    // Internal Signals
    reg          master_mode;
    reg  [5:0]   bit_cnt;
    reg  [5:0]   slot_cnt;
    reg          lrclk_reg;
    reg  [31:0]  tx_shift_reg;
    reg  [31:0]  rx_shift_reg;
    reg          tx_empty;
    reg          rx_full;
    reg          bclk_sync;
    reg          lrclk_sync;
    reg          bclk_d;
    reg          lrclk_d;

    // State Machine
    localparam IDLE  = 2'b00;
    localparam TX    = 2'b01;
    localparam RX    = 2'b10;

    reg [1:0]   state;

    // I/O
    assign bclk_o   = master_mode ? bclk_reg : 1'b0;
    assign bclk_t   = master_mode ? 1'b0 : 1'bz;
    assign lrclk_o  = master_mode ? lrclk_reg : 1'b0;
    assign lrclk_t  = master_mode ? 1'b0 : 1'bz;

    // BCLK and LRCLK generation (master mode)
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

    // LRCLK generation
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            lrclk_reg <= 1'b0;
        end else if (enable && master_mode) begin
            if (bit_cnt == DATA_WIDTH) begin
                lrclk_reg <= ~lrclk_reg;
            end
        end
    end

    // Synchronize external signals (slave mode)
    always @(posedge clk) begin
        bclk_d     <= bclk_i;
        bclk_sync  <= bclk_d;
        lrclk_d    <= lrclk_i;
        lrclk_sync <= lrclk_d;
    end

    // Bit counter
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            bit_cnt <= 6'd0;
        end else if (!enable) begin
            bit_cnt <= 6'd0;
        end else begin
            if (master_mode) begin
                if (bit_cnt == DATA_WIDTH - 1) begin
                    bit_cnt <= 6'd0;
                end else begin
                    bit_cnt <= bit_cnt + 1'b1;
                end
            end else begin
                if (bclk_sync && !bclk_d) begin
                    if (bit_cnt == DATA_WIDTH - 1) begin
                        bit_cnt <= 6'd0;
                    end else begin
                        bit_cnt <= bit_cnt + 1'b1;
                    end
                end
            end
        end
    end

    // Slot counter (channel counter)
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            slot_cnt <= 6'd0;
        end else if (!enable) begin
            slot_cnt <= 6'd0;
        end else begin
            if (bit_cnt == DATA_WIDTH - 1) begin
                if (slot_cnt == CHANNEL_NUM - 1) begin
                    slot_cnt <= 6'd0;
                end else begin
                    slot_cnt <= slot_cnt + 1'b1;
                end
            end
        end
    end

    // TX Shift Register
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            tx_shift_reg <= 32'd0;
            tx_empty     <= 1'b1;
        end else if (!enable) begin
            tx_shift_reg <= 32'd0;
            tx_empty     <= 1'b1;
        end else begin
            if (pcm_din_valid && tx_empty) begin
                tx_shift_reg <= pcm_din;
                tx_empty     <= 1'b0;
            end else if ((master_mode ? 1'b1 : bclk_sync) && !bclk_d) begin
                if (bit_cnt < DATA_WIDTH - 1) begin
                    tx_shift_reg <= {tx_shift_reg[30:0], 1'b0};
                end else begin
                    if (!tx_empty) begin
                        tx_empty <= 1'b1;
                    end
                end
            end
        end
    end

    // TX Data Output
    assign dout = tx_shift_reg[31];

    // RX Shift Register
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rx_shift_reg <= 32'd0;
            rx_full      <= 1'b0;
        end else if (!enable) begin
            rx_shift_reg <= 32'd0;
            rx_full      <= 1'b0;
        end else begin
            if ((master_mode ? 1'b1 : bclk_sync) && !bclk_d) begin
                rx_shift_reg <= {rx_shift_reg[30:0], din};
                if (bit_cnt == DATA_WIDTH - 1) begin
                    rx_full <= 1'b1;
                end
            end else if (pcm_dout_valid) begin
                rx_full <= 1'b0;
            end
        end
    end

    // RX Data Output
    assign pcm_dout       = rx_shift_reg;
    assign pcm_dout_valid = rx_full;

    // Control Register
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ctrl_reg <= 8'd0;
        end else begin
            if (pwrite && psel && penable) begin
                if (paddr == 8'h10) begin
                    ctrl_reg <= pwdata[7:0];
                end
            end
        end
    end

    // Master mode
    assign master_mode = ctrl_reg[0];

    // MCLK output
    assign mclk = clk;

    // Status Register
    assign stat_reg = {6'd0, rx_full, tx_empty};

endmodule
