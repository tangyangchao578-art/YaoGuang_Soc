//-----------------------------------------------------------------------------
// File: usb_30_phy.sv
// Description: USB 3.0 PHY Interface (SuperSpeed)
// Author: YaoGuang SoC Team
// Date: 2026-01-19
//-----------------------------------------------------------------------------

`timescale 1ps/1ps

module usb_30_phy_if #(
    parameter PORT_ID = 0
) (
    input  logic                                clk_phy,
    input  logic                                rst_n_phy,
    input  logic [9:0]                          tx_data,
    input  logic                                tx_valid,
    output logic                                tx_ready,
    input  logic                                tx_elec_idle,
    output logic                                phy_p,
    output logic                                phy_n,
    input  logic                                phy_rx_p,
    input  logic                                phy_rx_n,
    output logic [9:0]                          rx_data,
    output logic                                rx_valid,
    output logic                                rx_header_valid,
    input  logic                                rx_ready,
    output logic                                ref_clk_p,
    output logic                                ref_clk_n
);

    localparam PMA_WIDTH = 10;

    // 8b/10b Encoding Tables
    localparam [9:0] ENC_TABLE [0:255] = '{
        10'b1001110100, 10'b0111010000, 10'b1011010000, 10'b1100010000,
        10'b1001010000, 10'b1100100000, 10'b1001100000, 10'b1101100001,
        10'b1010100000, 10'b1010010000, 10'b1010001000, 10'b1001001000,
        10'b0100101000, 10'b0100100100, 10'b0011001000, 10'b0110001001,
        10'b1011000001, 10'b1010001010, 10'b1000101010, 10'b1000101001,
        10'b1001001001, 10'b0100010010, 10'b0010001010, 10'b0010001001,
        10'b0111001001, 10'b1011010001, 10'b0100010001, 10'b0010101001,
        10'b1001100001, 10'b0110001000, 10'b0100110001, 10'b1010010001,
        10'b1000110001, 10'b1000011001, 10'b1011000000, 10'b1011000100,
        10'b1000101100, 10'b0100010100, 10'b0100010011, 10'b0011000100,
        10'b0010011001, 10'b0100100101, 10'b0010010001, 10'b0010010010,
        10'b0110100100, 10'b0110100010, 10'b0010110001, 10'b0010110010,
        10'b0100110000, 10'b0100110011, 10'b0101010001, 10'b0101010010,
        10'b0100010101, 10'b0010100011, 10'b1001100100, 10'b0101001001,
        10'b0100110100, 10'b0011010001, 10'b0100000101, 10'b0011000001,
        10'b0100000110, 10'b0010100101, 10'b0100010000, 10'b1000100010,
        10'b1000010010, 10'b1000110100, 10'b1010010100, 10'b1001010010,
        10'b1001000101, 10'b0100100010, 10'b0010010101, 10'b0010011000,
        10'b0110000010, 10'b0101000101, 10'b0101010100, 10'b0101010011,
        10'b0100010110, 10'b0100100001, 10'b0100100100, 10'b0100101000,
        10'b0101000100, 10'b0101000010, 10'b0101000001, 10'b0011000010,
        10'b0011000101, 10'b0110010000, 10'b0110010011, 10'b0011001000,
        10'b0100001001, 10'b0011010010, 10'b0110100001, 10'b0110100101,
        10'b0010110100, 10'b0010110000, 10'b0010000101, 10'b0010001000,
        10'b0010000010, 10'b0100111000, 10'b0010010100, 10'b0011010000,
        10'b0110000100, 10'b0010000110, 10'b0100001010, 10'b1000001010,
        10'b1000001001, 10'b1001010001, 10'b1001000100, 10'b1010000100,
        10'b1010001000, 10'b1010011000, 10'b1010100010, 10'b1010101000,
        10'b1010010101, 10'b1010010010, 10'b1010001100, 10'b1010100100,
        10'b0100000010, 10'b0100001100, 10'b0100011000, 10'b0100010111,
        10'b0011000011, 10'b0010100001, 10'b0010100100, 10'b0010110101,
        10'b1001100010, 10'b1001100101, 10'b1011000101, 10'b1011000010,
        10'b1011001000, 10'b1011000110, 10'b1011010010, 10'b1011011000,
        10'b1010100001, 10'b1010011010, 10'b1000110000, 10'b1000110011,
        10'b1001010100, 10'b1001010011, 10'b1001000010, 10'b1001001100,
        10'b0110000101, 10'b0100101100, 10'b0100100011, 10'b0100110101,
        10'b0101100001, 10'b0101100010, 10'b0101011000, 10'b0101010110,
        10'b0101110000, 10'b0101110011, 10'b0101101000, 10'b0101100101,
        10'b0100101011, 10'b0100110001, 10'b0100110110, 10'b0100111010,
        10'b0101010000, 10'b0101001100, 10'b0101000011, 10'b0101000000,
        10'b0110010100, 10'b0110011000, 10'b0110001010, 10'b0110001001,
        10'b0110101000, 10'b0110100000, 10'b0110110000, 10'b0110110011,
        10'b0011110001, 10'b0011110010, 10'b0011100100, 10'b0011100010,
        10'b0011011000, 10'b0011010100, 10'b0011010011, 10'b0011001010,
        10'b0010101100, 10'b0010101010, 10'b0010100110, 10'b0010011100,
        10'b0000010100, 10'b0000010011, 10'b0000001100, 10'b0000001011,
        10'b0000011000, 10'b0000010110, 10'b0000010001, 10'b0000011110,
        10'b0000100100, 10'b0000100011, 10'b0000101100, 10'b0000101011,
        10'b0000110001, 10'b0000110110, 10'b0000110100, 10'b0000111010,
        10'b0001000101, 10'b0001000010, 10'b0001001001, 10'b0001001110,
        10'b0001010001, 10'b0001010110, 10'b0001010100, 10'b0001011010,
        10'b0001100101, 10'b0001100010, 10'b0001101001, 10'b0001101110,
        10'b0001110100, 10'b0001110001, 10'b0001110110, 10'b0001111010,
        10'b0010000101, 10'b0010001110, 10'b0010010101, 10'b0010010010,
        10'b0010100001, 10'b0010100110, 10'b0010101100, 10'b0010101010,
        10'b0010110001, 10'b0010110100, 10'b0010110011, 10'b0010111000,
        10'b0011000101, 10'b0011000010, 10'b0011001110, 10'b0011001010,
        10'b0011010001, 10'b0011010110, 10'b0011011100, 10'b0011011001,
        10'b0011100001, 10'b0011100100, 10'b0011101110, 10'b0011101010,
        10'b0011110000, 10'b0011110110, 10'b0011111001, 10'b0011111100
    };

    // TX Path
    logic [PMA_WIDTH-1:0]                        tx_ser_data;
    logic                                        tx_ser_valid;
    logic                                        tx_ser_ready;

    // RX Path
    logic [PMA_WIDTH-1:0]                        rx_ser_data;
    logic                                        rx_ser_valid;

    // 8b/10b Encoder
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            tx_ready <= 1'b0;
            tx_ser_valid <= 1'b0;
        end else begin
            if (tx_valid && tx_ready) begin
                tx_ser_data <= ENC_TABLE[tx_data];
                tx_ser_valid <= 1'b1;
                tx_ready <= 1'b0;
            end else if (tx_elec_idle) begin
                tx_ser_data <= 10'b1100001010;
                tx_ser_valid <= 1'b1;
            end else if (tx_ser_ready) begin
                tx_ser_valid <= 1'b0;
                tx_ready <= 1'b1;
            end
        end
    end

    // Serialization
    always_ff @(posedge clk_phy) begin
        tx_ser_data <= tx_ser_data;
        if (tx_ser_valid) begin
            tx_ser_ready <= 1'b1;
        end
    end

    // Deserialization
    always_ff @(posedge clk_phy) begin
        rx_ser_data <= {phy_rx_p, phy_rx_n};
        rx_ser_valid <= 1'b1;
    end

    // 8b/10b Decoder
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            rx_valid <= 1'b0;
            rx_data <= '0;
            rx_header_valid <= 1'b0;
        end else begin
            rx_valid <= rx_ser_valid;
            if (rx_ser_valid) begin
                rx_data <= invert_dec_data(rx_ser_data);
                rx_header_valid <= (rx_ser_data == 10'b0011111010);
            end
        end
    endfunction invert_dec_data(input [9:0] data);
        integer i;
        begin
            for (i = 0; i < 10; i++) begin
                invert_dec_data[i] = data[9-i];
            end
        end
    endfunction

    // Reference Clock Output
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            ref_clk_p <= 1'b0;
            ref_clk_n <= 1'b1;
        end else begin
            ref_clk_p <= !ref_clk_p;
            ref_clk_n <= ref_clk_p;
        end
    end

    // PHY Output
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            phy_p <= 1'b0;
            phy_n <= 1'b1;
        end else begin
            if (tx_ser_valid) begin
                phy_p <= tx_ser_data[0];
                phy_n <= !tx_ser_data[0];
            end else begin
                phy_p <= 1'b0;
                phy_n <= 1'b1;
            end
        end
    end

endmodule
