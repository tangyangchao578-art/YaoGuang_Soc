//-----------------------------------------------------------------------------
// File: pcie_phy_if.sv
// Description: PCIe PHY Interface Module
// Author: YaoGuang SoC Team
// Date: 2026-01-19
//-----------------------------------------------------------------------------

`timescale 1ps/1ps

module pcie_phy_if #(
    parameter LANES = 8,
    parameter PHY_DATA_WIDTH = 32
) (
    input  logic                                clk_phy,
    input  logic                                rst_n_phy,
    output logic [LANES*PHY_DATA_WIDTH-1:0]     phy_tx_data,
    input  logic [LANES*PHY_DATA_WIDTH-1:0]     phy_rx_data,
    output logic                                phy_tx_valid,
    input  logic                                phy_rx_valid,
    output logic                                phy_tx_ready,
    input  logic                                phy_rx_ready,
    output logic [5:0]                          phy_tx_status,
    input  logic [5:0]                          phy_rx_status,
    output logic [LANES-1:0]                    tx_data_p,
    output logic [LANES-1:0]                    tx_data_n,
    input  logic [LANES-1:0]                    rx_data_p,
    input  logic [LANES-1:0]                    rx_data_n,
    output logic                                tx_clk_p,
    output logic                                tx_clk_n,
    input  logic                                rx_clk_p,
    input  logic                                rx_clk_n,
    output logic                                tx_elec_idle,
    input  logic                                phy_ready,
    input  logic                                phy_status
);

    localparam DATA_WIDTH_PER_LANE = PHY_DATA_WIDTH / LANES;

    logic [PHY_DATA_WIDTH-1:0]                  tx_data_reg;
    logic [PHY_DATA_WIDTH-1:0]                  rx_data_reg;
    logic                                        tx_valid_reg;
    logic                                        rx_valid_reg;
    logic [LANES-1:0]                            lane_select;
    logic [7:0]                                  scrambler_state;
    logic                                        scrambler_enable;
    logic [15:0]                                 tx_skip_interval;
    logic                                        skip_insert;
    logic                                        skip_remove;

    // 8b/10b Encoding State Machine
    typedef enum logic [2:0] {
        IDLE_ENC,
        DATA_ENC,
        SKIP_ENC,
        COM_ENC
    } enc_state_t;

    enc_state_t enc_state;

    // 8b/10b Decoding State Machine
    typedef enum logic [2:0] {
        IDLE_DEC,
        DATA_DEC,
        SKIP_DEC,
        COM_DEC,
        ERROR_DEC
    } dec_state_t;

    dec_state_t dec_state;

    // TX Data Path
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            tx_data_reg <= '0;
            tx_valid_reg <= 1'b0;
            scrambler_state <= 8'hFF;
            skip_insert <= 1'b0;
            enc_state <= IDLE_ENC;
        end else begin
            tx_valid_reg <= phy_tx_valid;
            if (phy_tx_valid && phy_tx_ready) begin
                tx_data_reg <= phy_tx_data[PHY_DATA_WIDTH-1:0];
                scrambler_state <= next_scrambler_state(scrambler_state, scrambler_enable);
                skip_insert <= (tx_skip_interval == 0) && scrambler_enable;
                enc_state <= DATA_ENC;
            end else if (skip_insert) begin
                tx_data_reg <= {10'b0011111010, 10'b0011111010, 10'b0011111010};
                enc_state <= SKIP_ENC;
            end else if (phy_rx_valid && !scrambler_enable) begin
                enc_state <= IDLE_ENC;
            end
        end
    end

    // RX Data Path
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            rx_data_reg <= '0;
            rx_valid_reg <= 1'b0;
            skip_remove <= 1'b0;
            dec_state <= IDLE_DEC;
        end else begin
            rx_data_reg <= phy_rx_data[PHY_DATA_WIDTH-1:0];
            rx_valid_reg <= phy_rx_valid;
            if (phy_rx_valid) begin
                if (phy_rx_data == {10{10'b1100001010}}) begin
                    skip_remove <= 1'b1;
                    dec_state <= COM_DEC;
                end else if (skip_remove && (phy_rx_data == {10{10'b0011111010}})) begin
                    skip_remove <= 1'b0;
                    dec_state <= DATA_DEC;
                end else begin
                    dec_state <= DATA_DEC;
                end
            end
        end
    end

    // Lane Deskew and Alignment
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            lane_select <= '0;
        end else if (phy_rx_valid) begin
            for (int i = 0; i < LANES; i++) begin
                if (phy_rx_data[i*10+:10] == 10'b1100001010) begin
                    lane_select[i] <= 1'b1;
                end
            end
        end
    function [7:0] next_scrambler_state(input [7:0] state, input enable);
        if (enable) begin
            next_scrambler_state = {state[6:0], state[7] ^ state[5] ^ state[4] ^ state[2]};
        end else begin
            next_scrambler_state = state;
        end
    endfunction

    // PHY Control Signals
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            tx_elec_idle <= 1'b1;
            phy_tx_status <= '0;
            tx_skip_interval <= 16'd118;
        end else begin
            phy_tx_status[0] <= phy_ready;
            phy_tx_status[1] <= link_up();
            if (power_state == D0) begin
                tx_elec_idle <= 1'b0;
            end else begin
                tx_elec_idle <= 1'b1;
            end
            if (tx_skip_interval > 0) begin
                tx_skip_interval <= tx_skip_interval - 1;
            end
        end
    endfunction link_up = (phy_status[0] && phy_status[1]);

    // Electrical Idle Control
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            tx_elec_idle <= 1'b1;
        end else begin
            if (!phy_ready || (power_state == D3)) begin
                tx_elec_idle <= 1'b1;
            end else if (link_training) begin
                tx_elec_idle <= tx_elec_idle;
            end else begin
                tx_elec_idle <= 1'b0;
            end
        end
    end

    // Polarity Inversion Correction
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            for (int i = 0; i < LANES; i++) begin
                rx_data_p[i] <= rx_data_p[i];
                rx_data_n[i] <= rx_data_n[i];
            end
        end else begin
            if (polarity_inverted[i]) begin
                rx_data_p[i] <= rx_data_n[i];
                rx_data_n[i] <= rx_data_p[i];
            end
        end
    end

endmodule
