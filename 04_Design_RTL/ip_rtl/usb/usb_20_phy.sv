//-----------------------------------------------------------------------------
// File: usb_20_phy.sv
// Description: USB 2.0 PHY (High-Speed/Full-Speed/Low-Speed)
// Author: YaoGuang SoC Team
// Date: 2026-01-19
//-----------------------------------------------------------------------------

`timescale 1ps/1ps

module usb_20_phy #(
    parameter PORT_ID = 0
) (
    input  logic                                clk_phy,
    input  logic                                rst_n_phy,
    input  logic                                tx_data,
    input  logic                                tx_se0,
    output logic                                tx_oe,
    input  logic                                rx_dp,
    input  logic                                rx_dn,
    output logic                                rx_valid,
    output logic                                rx_data,
    output logic                                phy_ready,
    output logic                                phy_status
);

    localparam HS_BIT_RATE = 480000000;
    localparam FS_BIT_RATE = 12000000;
    localparam LS_BIT_RATE = 1500000;

    // PHY State Machine
    typedef enum logic [2:0] {
        PHY_IDLE,
        PHY_CHIRP,
        PHY_RESET,
        PHY_HS_SYNC,
        PHY_HS_DATA,
        PHY_FS_SYNC,
        PHY_FS_DATA,
        PHY_LS_DATA
    } phy_state_t;

    phy_state_t phy_state;

    // Clock Recovery
    logic                                        rx_clk_rec;
    logic [3:0]                                  clk_div;
    logic                                        bit_boundary;
    logic [7:0]                                  bit_counter;
    logic                                        rx_sample;

    // Synchronizer
    logic                                        rx_dp_sync;
    logic                                        rx_dn_sync;

    // Data Recovery
    logic [7:0]                                  rx_shift_reg;
    logic                                        rx_valid_reg;
    logic                                        rx_bit_stuff;
    logic [5:0]                                  bit_stuff_cnt;

    // HS Termination
    logic                                        hs_termination;
    logic                                        fs_termination;

    // Line State
    logic [1:0]                                  line_state;
    logic                                        se0_detect;
    logic                                        j_state;
    logic                                        k_state;

    // Chirp Generation
    logic                                        chirp_enable;
    logic                                        chirp_data;

    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            phy_state <= PHY_IDLE;
            phy_ready <= 1'b0;
            hs_termination <= 1'b0;
            fs_termination <= 1'b1;
        end else begin
            case (phy_state)
                PHY_IDLE: begin
                    if (rx_dp && !rx_dn) begin
                        phy_state <= PHY_CHIRP;
                        phy_ready <= 1'b1;
                    end
                end
                PHY_CHIRP: begin
                    chirp_enable <= 1'b1;
                    if (line_state == 2'b01) begin
                        phy_state <= PHY_RESET;
                    end
                end
                PHY_RESET: begin
                    if (line_state == 2'b10) begin
                        phy_state <= PHY_HS_SYNC;
                    end else if (line_state == 2'b01) begin
                        phy_state <= PHY_FS_SYNC;
                    end
                end
                PHY_HS_SYNC: begin
                    hs_termination <= 1'b1;
                    fs_termination <= 1'b0;
                    if (bit_counter == 8'd32) begin
                        phy_state <= PHY_HS_DATA;
                    end
                end
                PHY_HS_DATA: begin
                    rx_valid <= rx_valid_reg;
                    rx_data <= rx_shift_reg[0];
                end
                PHY_FS_SYNC: begin
                    fs_termination <= 1'b1;
                    if (bit_counter == 8'd32) begin
                        phy_state <= PHY_FS_DATA;
                    end
                end
                PHY_FS_DATA: begin
                    rx_valid <= rx_valid_reg;
                    rx_data <= rx_shift_reg[0];
                end
            endcase
        end
    end

    // Input Synchronizer
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            rx_dp_sync <= 1'b0;
            rx_dn_sync <= 1'b0;
        end else begin
            rx_dp_sync <= rx_dp;
            rx_dn_sync <= rx_dn;
        end
    end

    // Line State Detection
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            line_state <= 2'b00;
            se0_detect <= 1'b0;
            j_state <= 1'b0;
            k_state <= 1'b0;
        end else begin
            line_state <= {rx_dp_sync, rx_dn_sync};
            se0_detect <= !rx_dp_sync && !rx_dn_sync;
            j_state <= rx_dp_sync && !rx_dn_sync;
            k_state <= !rx_dp_sync && rx_dn_sync;
        end
    end

    // Bit Sampling
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            bit_counter <= '0;
            rx_sample <= 1'b0;
            clk_div <= '0;
        end else begin
            clk_div <= clk_div + 1;
            if (clk_div == 4'd7) begin
                rx_sample <= 1'b1;
                bit_counter <= bit_counter + 1;
            end else begin
                rx_sample <= 1'b0;
            end
        end
    end

    // Bit Stuffing Detection
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            bit_stuff_cnt <= '0;
            rx_bit_stuff <= 1'b0;
            rx_valid_reg <= 1'b0;
            rx_shift_reg <= '0;
        end else begin
            if (rx_sample) begin
                if (bit_stuff_cnt == 6'd63) begin
                    rx_bit_stuff <= 1'b1;
                    bit_stuff_cnt <= '0;
                end else begin
                    rx_bit_stuff <= 1'b0;
                    if (line_state[0]) begin
                        bit_stuff_cnt <= bit_stuff_cnt + 1;
                    end else begin
                        bit_stuff_cnt <= '0;
                    end
                end
                if (!rx_bit_stuff) begin
                    rx_shift_reg <= {line_state[0], rx_shift_reg[7:1]};
                    rx_valid_reg <= 1'b1;
                end else begin
                    rx_valid_reg <= 1'b0;
                end
            end else begin
                rx_valid_reg <= 1'b0;
            end
        end
    end

    // TX Output Control
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            tx_oe <= 1'b0;
        end else begin
            tx_oe <= (phy_state != PHY_IDLE) && !se0_detect;
        end
    end

    // TX Data Output
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            tx_dp_reg <= 1'b0;
            tx_dn_reg <= 1'b0;
        end else begin
            if (tx_se0) begin
                tx_dp_reg <= 1'b0;
                tx_dn_reg <= 1'b0;
            end else if (tx_data) begin
                tx_dp_reg <= 1'b1;
                tx_dn_reg <= 1'b0;
            end else begin
                tx_dp_reg <= 1'b0;
                tx_dn_reg <= 1'b1;
            end
        end
    end

    // PHY Status Output
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            phy_status <= 1'b0;
        end else begin
            phy_status <= (phy_state != PHY_IDLE);
        end
    end

endmodule
