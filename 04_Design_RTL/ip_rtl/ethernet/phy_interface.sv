//-----------------------------------------------------------------------------
// File: phy_interface.sv
// Description: PHY Interface (MII/GMII/RGMII/XGMII)
// Author: YaoGuang SoC Team
// Date: 2026-01-19
//-----------------------------------------------------------------------------

`timescale 1ps/1ps

module phy_interface #(
    parameter PORT_ID = 0
) (
    input  logic                                clk_sys,
    input  logic                                clk_phy,
    input  logic                                rst_n_sys,
    input  logic                                rst_n_phy,
    input  logic                                mac_tx_clk,
    input  logic                                mac_rx_clk,
    input  logic                                mac_tx_en,
    input  logic                                mac_tx_err,
    input  logic [7:0]                          mac_tx_data,
    output logic                                mac_rx_dv,
    output logic                                mac_rx_err,
    output logic [7:0]                          mac_rx_data,
    input  logic                                mac_col,
    input  logic                                mac_crs,
    output logic                                phy_tx_clk,
    output logic                                phy_rx_clk,
    output logic                                phy_tx_en,
    output logic                                phy_tx_err,
    output logic [7:0]                          phy_tx_data,
    input  logic                                phy_rx_dv,
    input  logic                                phy_rx_err,
    input  logic [7:0]                          phy_rx_data,
    output logic                                phy_col,
    output logic                                phy_crs,
    input  logic                                phy_reset_n,
    output logic                                rgmii_tx_clk,
    output logic                                rgmii_tx_ctl,
    output logic [3:0]                          rgmii_txd,
    input  logic                                rgmii_rx_clk,
    input  logic                                rgmii_rx_ctl,
    input  logic [3:0]                          rgmii_rxd,
    output logic                                xgmii_tx_clk,
    output logic                                xgmii_tx_ctl,
    output logic [63:0]                         xgmii_txd,
    input  logic                                xgmii_rx_clk,
    input  logic                                xgmii_rx_ctl,
    input  logic [63:0]                         xgmii_rxd
);

    // PHY Mode Selection
    typedef enum logic [2:0] {
        PHY_MODE_MII,
        PHY_MODE_GMII,
        PHY_MODE_RGMII,
        PHY_MODE_XGMII,
        PHY_MODE_XLGMII
    } phy_mode_t;

    phy_mode_t                                   phy_mode;
    logic                                        rgmii_id_delay;
    logic                                        rgmii_clk_delay;

    // MII/GMII to RGMII Conversion
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            rgmii_tx_ctl <= 1'b0;
            rgmii_txd <= '0;
        end else begin
            rgmii_tx_ctl <= mac_tx_en;
            if (mac_tx_en) begin
                rgmii_txd <= mac_tx_data[3:0];
            end else begin
                rgmii_txd <= '0;
            end
        end
    end

    // RGMII to MII/GMII Conversion
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            mac_rx_dv <= 1'b0;
            mac_rx_err <= 1'b0;
            mac_rx_data <= '0;
        end else begin
            mac_rx_dv <= rgmii_rx_ctl;
            mac_rx_err <= phy_rx_err;
            mac_rx_data <= {4'b0, rgmii_rxd};
        end
    end

    // RGMII Input Delay Compensation
    always_ff @(posedge rgmii_rx_clk or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            rgmii_rx_ctl_reg <= 1'b0;
            rgmii_rxd_reg <= '0;
        end else begin
            rgmii_rx_ctl_reg <= rgmii_rx_ctl;
            rgmii_rxd_reg <= rgmii_rxd;
        end
    end

    // RGMII Clock Delay for Input
    IDELAYE2 #(
        .IDELAY_TYPE("FIXED"),
        .IDELAY_VALUE(0),
        .REFCLK_FREQUENCY(200.0)
    ) u_rgmii_clk_delay (
        .C(clk_phy),
        .REGRST(rst_n_phy),
        .IDATAIN(rgmii_rx_clk),
        .DATAOUT(rgmii_rx_clk_delayed)
    );

    // XGMII Conversion
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            xgmii_tx_ctl <= 1'b0;
            xgmii_txd <= '0;
        end else begin
            xgmii_tx_ctl <= mac_tx_en;
            xgmii_txd <= {8{mac_tx_data}};
        end
    end

    always_ff @(posedge xgmii_rx_clk or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            mac_rx_dv <= 1'b0;
            mac_rx_err <= 1'b0;
            mac_rx_data <= '0;
        end else begin
            mac_rx_dv <= xgmii_rx_ctl;
            mac_rx_err <= |xgmii_rxd[63:56];
            mac_rx_data <= xgmii_rxd[63:56];
        end
    end

    // PHY Reset Generation
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            phy_reset_n_reg <= 1'b0;
        end else begin
            if (phy_reset_counter < 32'd100) begin
                phy_reset_n_reg <= 1'b0;
                phy_reset_counter <= phy_reset_counter + 1;
            end else begin
                phy_reset_n_reg <= 1'b1;
            end
        end
    end

    // PHY Mode Detection
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            phy_mode <= PHY_MODE_RGMII;
        end else begin
            case (link_speed_detected)
                2'b11: phy_mode <= PHY_MODE_XGMII;
                2'b10: phy_mode <= PHY_MODE_RGMII;
                2'b01: phy_mode <= PHY_MODE_GMII;
                default: phy_mode <= PHY_MODE_MII;
            endcase
        end
    end

    // Clock Generation for Different Modes
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            phy_tx_clk <= 1'b0;
        end else begin
            case (phy_mode)
                PHY_MODE_MII: begin
                    phy_tx_clk <= !phy_tx_clk;
                end
                PHY_MODE_GMII: begin
                    phy_tx_clk <= !phy_tx_clk;
                end
                PHY_MODE_RGMII: begin
                    rgmii_tx_clk <= !rgmii_tx_clk;
                end
                PHY_MODE_XGMII: begin
                    xgmii_tx_clk <= !xgmii_tx_clk;
                end
            endcase
        end
    end

    // Collision and Carrier Sense
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            phy_col <= 1'b0;
            phy_crs <= 1'b0;
        end else begin
            if (duplex_mode == 1'b0) begin
                phy_col <= mac_col;
                phy_crs <= mac_crs;
            end else begin
                phy_col <= 1'b0;
                phy_crs <= 1'b1;
            end
        end
    end

endmodule
