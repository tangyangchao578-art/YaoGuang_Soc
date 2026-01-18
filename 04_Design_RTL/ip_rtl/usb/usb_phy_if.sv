//-----------------------------------------------------------------------------
// File: usb_phy_if.sv
// Description: USB PHY Interface Wrapper
// Author: YaoGuang SoC Team
// Date: 2026-01-19
//-----------------------------------------------------------------------------

`timescale 1ps/1ps

module usb_phy_if #(
    parameter PORT_ID = 0
) (
    input  logic                                clk_phy,
    input  logic                                rst_n_phy,
    input  logic                                usb3_enable,
    output logic                                phy_ready,
    input  logic                                phy_status,
    input  logic                                usb2_rx_dp,
    input  logic                                usb2_rx_dn,
    output logic                                usb2_tx_dp,
    output logic                                usb2_tx_dn,
    output logic                                usb2_tx_oe,
    input  logic                                usb2_rx_valid,
    output logic                                usb2_rx_data,
    output logic                                usb3_tx_p,
    output logic                                usb3_tx_n,
    input  logic                                usb3_rx_p,
    input  logic                                usb3_rx_n,
    output logic                                usb3_tx_elec_idle,
    input  logic [9:0]                          usb3_tx_data,
    input  logic                                usb3_tx_valid,
    output logic                                usb3_tx_ready,
    output logic [9:0]                          usb3_rx_data,
    output logic                                usb3_rx_valid,
    output logic                                usb3_rx_header_valid,
    input  logic                                usb3_rx_ready,
    output logic                                ref_clk_p,
    output logic                                ref_clk_n
);

    // PHY Mode Selection
    logic                                        phy_mode_usb2;
    logic                                        phy_mode_usb3;

    // USB 2.0 Signal Control
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            usb2_tx_oe <= 1'b0;
            phy_mode_usb2 <= 1'b0;
            phy_mode_usb3 <= 1'b0;
        end else begin
            if (usb3_enable) begin
                phy_mode_usb2 <= 1'b0;
                phy_mode_usb3 <= 1'b1;
                usb2_tx_oe <= 1'b0;
            end else begin
                phy_mode_usb2 <= 1'b1;
                phy_mode_usb3 <= 1'b0;
                usb2_tx_oe <= usb2_tx_oe_reg;
            end
        end
    end

    // USB 2.0 Data Path
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            usb2_tx_dp <= 1'b0;
            usb2_tx_dn <= 1'b0;
        end else begin
            if (phy_mode_usb2) begin
                if (usb2_tx_data) begin
                    usb2_tx_dp <= 1'b1;
                    usb2_tx_dn <= 1'b0;
                end else begin
                    usb2_tx_dp <= 1'b0;
                    usb2_tx_dn <= 1'b1;
                end
            end else begin
                usb2_tx_dp <= 1'b0;
                usb2_tx_dn <= 1'b0;
            end
        end
    end

    // USB 3.0 Data Path
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            usb3_tx_elec_idle <= 1'b1;
            usb3_tx_ready <= 1'b0;
        end else begin
            if (phy_mode_usb3) begin
                if (usb3_tx_valid && usb3_tx_ready) begin
                    usb3_tx_elec_idle <= 1'b0;
                end else if (usb3_tx_elec_idle) begin
                    usb3_tx_elec_idle <= 1'b0;
                end
            end else begin
                usb3_tx_elec_idle <= 1'b1;
            end
        end
    end

    // Reference Clock Generation
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            ref_clk_p <= 1'b0;
            ref_clk_n <= 1'b1;
        end else begin
            ref_clk_p <= !ref_clk_p;
            ref_clk_n <= !ref_clk_p;
        end
    end

    // PHY Ready Generation
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            phy_ready <= 1'b0;
        end else begin
            phy_ready <= phy_status;
        end
    end

endmodule
