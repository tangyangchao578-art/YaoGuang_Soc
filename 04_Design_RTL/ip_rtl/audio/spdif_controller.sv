// Copyright (c) 2026 YaoGuang SoC Project
// All rights reserved

// SPDIF Controller Module
// Revision: 1.0
// Date: 2026-01-18

`timescale 1ns/1ps

module spdif_controller (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         enable,

    // External SPDIF Interface
    input  wire         spdif_rx,
    output wire         spdif_tx,

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

    // Internal Signals
    reg          tx_enable;
    reg          rx_enable;
    reg  [31:0]  tx_data_reg;
    reg  [31:0]  rx_data_reg;
    reg          tx_valid_reg;
    reg          rx_valid_reg;
    reg  [5:0]   bit_cnt;
    reg  [5:0]   symbol_cnt;
    reg          prev_rx;
    reg          rx_edge;
    reg          rx_bit;
    reg  [31:0]  rx_shift_reg;
    reg  [63:0]  tx_shift_reg;
    reg          tx_bit;
    reg          tx_prev_bit;

    // Decoder state machine
    localparam RX_IDLE    = 3'b000;
    localparam RX_SYNC    = 3'b001;
    localparam RX_DATA    = 3'b010;
    localparam RX_PARITY  = 3'b011;
    localparam RX_DONE    = 3'b100;

    reg [2:0]   rx_state;

    // Encoder state machine
    localparam TX_IDLE    = 2'b00;
    localparam TX_ENCODE  = 2'b01;
    localparam TX_TRANSMIT = 2'b10;

    reg [1:0]   tx_state;

    // Parity calculation
    reg  [5:0]   parity_cnt;
    wire        parity_bit;

    // SPDIF TX Output
    assign spdif_tx = tx_bit;

    // RX Input synchronization
    always @(posedge clk) begin
        prev_rx <= spdif_rx;
        rx_edge <= spdif_rx && !prev_rx;
    end

    // RX Decoder
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rx_state     <= RX_IDLE;
            rx_data_reg  <= 32'd0;
            rx_valid_reg <= 1'b0;
            bit_cnt      <= 6'd0;
            symbol_cnt   <= 6'd0;
            rx_shift_reg <= 32'd0;
        end else if (!enable || !rx_enable) begin
            rx_state     <= RX_IDLE;
            rx_data_reg  <= 32'd0;
            rx_valid_reg <= 1'b0;
            bit_cnt      <= 6'd0;
            symbol_cnt   <= 6'd0;
            rx_shift_reg <= 32'd0;
        end else begin
            case (rx_state)
                RX_IDLE: begin
                    rx_valid_reg <= 1'b0;
                    if (rx_edge) begin
                        rx_state <= RX_SYNC;
                        bit_cnt <= 6'd0;
                    end
                end

                RX_SYNC: begin
                    if (rx_edge) begin
                        bit_cnt <= bit_cnt + 1'b1;
                        if (bit_cnt == 6'd2) begin
                            rx_state <= RX_DATA;
                            bit_cnt <= 6'd0;
                            symbol_cnt <= 6'd0;
                            rx_shift_reg <= 32'd0;
                        end
                    end
                end

                RX_DATA: begin
                    if (rx_edge) begin
                        rx_shift_reg <= {rx_shift_reg[30:0], rx_bit};
                        bit_cnt <= bit_cnt + 1'b1;
                        if (bit_cnt == 6'd31) begin
                            rx_state <= RX_PARITY;
                            bit_cnt <= 6'd0;
                        end
                    end
                end

                RX_PARITY: begin
                    if (rx_edge) begin
                        bit_cnt <= bit_cnt + 1'b1;
                        if (bit_cnt == 6'd1) begin
                            rx_state <= RX_DONE;
                        end
                    end
                end

                RX_DONE: begin
                    rx_data_reg <= rx_shift_reg;
                    rx_valid_reg <= 1'b1;
                    rx_state <= RX_IDLE;
                end
            end
        end
    end

    // BMC Decoder (extract data bit from BMC)
    always @(posedge clk) begin
        if (rx_edge) begin
            if (prev_rx == spdif_rx) begin
                rx_bit <= 1'b0;
            end else begin
                rx_bit <= 1'b1;
            end
        end
    end

    // TX Encoder
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            tx_state    <= TX_IDLE;
            tx_bit      <= 1'b1;
            tx_shift_reg <= 64'd0;
            bit_cnt     <= 6'd0;
            tx_valid_reg <= 1'b0;
        end else if (!enable || !tx_enable) begin
            tx_state    <= TX_IDLE;
            tx_bit      <= 1'b1;
            bit_cnt     <= 6'd0;
        end else begin
            case (tx_state)
                TX_IDLE: begin
                    tx_valid_reg <= 1'b0;
                    tx_bit <= 1'b1;
                    if (pcm_din_valid) begin
                        tx_data_reg <= pcm_din;
                        tx_state <= TX_ENCODE;
                        parity_cnt <= 6'd0;
                        tx_shift_reg <= 64'd0;
                    end
                end

                TX_ENCODE: begin
                    // Parity calculation
                    parity_cnt <= parity_cnt + pcm_din[bit_cnt[4:0]];

                    // BMC encoding
                    if (bit_cnt == 6'd0) begin
                        tx_bit <= 1'b1; // Start with 1 for transition
                    end else begin
                        if (pcm_din[bit_cnt[4:0]] == tx_prev_bit) begin
                            tx_bit <= 1'b0;
                        end else begin
                            tx_bit <= 1'b1;
                        end
                    end
                    tx_prev_bit <= tx_bit;

                    tx_shift_reg <= {tx_shift_reg[62:0], tx_bit};
                    bit_cnt <= bit_cnt + 1'b1;

                    if (bit_cnt == 6'd31) begin
                        // Add parity bit
                        if (parity_cnt[0] == tx_prev_bit) begin
                            tx_bit <= 1'b0;
                        end else begin
                            tx_bit <= 1'b1;
                        end
                        tx_shift_reg <= {tx_shift_reg[62:0], tx_bit};
                        tx_prev_bit <= tx_bit;
                        tx_state <= TX_TRANSMIT;
                        bit_cnt <= 6'd0;
                    end
                end

                TX_TRANSMIT: begin
                    tx_bit <= tx_shift_reg[63];
                    tx_shift_reg <= {tx_shift_reg[62:0], 1'b0};
                    bit_cnt <= bit_cnt + 1'b1;

                    if (bit_cnt == 6'd64) begin
                        tx_valid_reg <= 1'b1;
                        tx_state <= TX_IDLE;
                    end
                end
            end
        end
    end

    // Output assignments
    assign pcm_dout       = rx_data_reg;
    assign pcm_dout_valid = rx_valid_reg;

    // Control Register
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ctrl_reg <= 8'd0;
        end else begin
            if (pwrite && psel && penable) begin
                if (paddr == 8'h28) begin
                    ctrl_reg <= pwdata[7:0];
                end
            end
        end
    end

    // Decode control fields
    always @(posedge clk) begin
        tx_enable <= ctrl_reg[0];
        rx_enable <= ctrl_reg[1];
    end

endmodule
