//-----------------------------------------------------------------------------
// File: ethernet_top.sv
// Description: 10G/1G Ethernet Controller Top Level
// Author: YaoGuang SoC Team
// Date: 2026-01-19
//-----------------------------------------------------------------------------

`timescale 1ps/1ps

module ethernet_top #(
    parameter PORT_COUNT = 2,
    parameter MAX_CHANNELS = 8,
    parameter AXI_DATA_WIDTH = 256,
    parameter AXI_ADDR_WIDTH = 48,
    parameter TSN_ENABLE = 1
) (
    input  logic                                clk_sys,
    input  logic                                clk_phy,
    input  logic                                rst_n_sys,
    input  logic                                rst_n_phy,

    // AXI4 Slave Interface (Management)
    input  logic [AXI_ADDR_WIDTH-1:0]           s_axibus_awaddr,
    input  logic [3:0]                          s_axibus_awid,
    input  logic [7:0]                          s_axibus_awlen,
    input  logic [2:0]                          s_axibus_awsize,
    input  logic [1:0]                          s_axibus_awburst,
    input  logic                                s_axibus_awvalid,
    output logic                                s_axibus_awready,
    input  logic [AXI_DATA_WIDTH-1:0]           s_axibus_wdata,
    input  logic [(AXI_DATA_WIDTH/8)-1:0]       s_axibus_wstrb,
    input  logic                                s_axibus_wlast,
    input  logic                                s_axibus_wvalid,
    output logic                                s_axibus_wready,
    output logic [1:0]                          s_axibus_bresp,
    output logic                                s_axibus_bvalid,
    input  logic                                s_axibus_bready,
    input  logic [AXI_ADDR_WIDTH-1:0]           s_axibus_araddr,
    input  logic [3:0]                          s_axibus_arid,
    input  logic [7:0]                          s_axibus_arlen,
    input  logic [2:0]                          s_axibus_arsize,
    input  logic [1:0]                          s_axibus_arburst,
    input  logic                                s_axibus_arvalid,
    output logic                                s_axibus_arready,
    output logic [AXI_DATA_WIDTH-1:0]           s_axibus_rdata,
    output logic [1:0]                          s_axibus_rresp,
    output logic                                s_axibus_rlast,
    output logic                                s_axibus_rvalid,
    input  logic                                s_axibus_rready,

    // AXI4-Stream TX (to PHY)
    output logic [PORT_COUNT-1:0]               tx_axis_tvalid,
    output logic [PORT_COUNT-1:0]               tx_axis_tlast,
    output logic [PORT_COUNT*7:0]               tx_axis_tuser,
    output logic [PORT_COUNT*127:0]             tx_axis_tdata,
    input  logic [PORT_COUNT-1:0]               tx_axis_tready,

    // AXI4-Stream RX (from PHY)
    input  logic [PORT_COUNT-1:0]               rx_axis_tvalid,
    input  logic [PORT_COUNT-1:0]               rx_axis_tlast,
    input  logic [PORT_COUNT*7:0]               rx_axis_tuser,
    input  logic [PORT_COUNT*127:0]             rx_axis_tdata,
    output logic [PORT_COUNT-1:0]               rx_axis_tready,

    // PHY MII Interface
    input  logic [PORT_COUNT-1:0]               phy_tx_clk,
    input  logic [PORT_COUNT-1:0]               phy_rx_clk,
    output logic [PORT_COUNT-1:0]               phy_tx_en,
    output logic [PORT_COUNT-1:0]               phy_tx_err,
    output logic [PORT_COUNT*7:0]               phy_tx_data,
    input  logic [PORT_COUNT-1:0]               phy_rx_dv,
    input  logic [PORT_COUNT-1:0]               phy_rx_err,
    input  logic [PORT_COUNT*7:0]               phy_rx_data,
    output logic [PORT_COUNT-1:0]               phy_col,
    output logic [PORT_COUNT-1:0]               phy_crs,
    input  logic [PORT_COUNT-1:0]               phy_reset_n,

    // RGMII Interface
    output logic [PORT_COUNT-1:0]               rgmii_tx_clk,
    output logic [PORT_COUNT-1:0]               rgmii_tx_ctl,
    output logic [PORT_COUNT*4:0]               rgmii_txd,
    input  logic [PORT_COUNT-1:0]               rgmii_rx_clk,
    input  logic [PORT_COUNT-1:0]               rgmii_rx_ctl,
    input  logic [PORT_COUNT*4:0]               rgmii_rxd,

    // XGMII Interface
    output logic [PORT_COUNT-1:0]               xgmii_tx_clk,
    output logic [PORT_COUNT-1:0]               xgmii_tx_ctl,
    output logic [PORT_COUNT*64:0]              xgmii_txd,
    input  logic [PORT_COUNT-1:0]               xgmii_rx_clk,
    input  logic [PORT_COUNT-1:0]               xgmii_rx_ctl,
    input  logic [PORT_COUNT*64:0]              xgmii_rxd,

    // DMA Interface
    output logic [PORT_COUNT*MAX_CHANNELS*AXI_ADDR_WIDTH-1:0] dma_araddr,
    output logic [PORT_COUNT*MAX_CHANNELS*4-1:0]               dma_arlen,
    output logic [PORT_COUNT*MAX_CHANNELS-1:0]                 dma_arvalid,
    input  logic [PORT_COUNT*MAX_CHANNELS-1:0]                 dma_arready,
    input  logic [PORT_COUNT*MAX_CHANNELS*AXI_DATA_WIDTH-1:0]  dma_rdata,
    input  logic [PORT_COUNT*MAX_CHANNELS-1:0]                 dma_rvalid,
    input  logic [PORT_COUNT*MAX_CHANNELS-1:0]                 dma_rlast,
    output logic [PORT_COUNT*MAX_CHANNELS*AXI_ADDR_WIDTH-1:0]  dma_awaddr,
    output logic [PORT_COUNT*MAX_CHANNELS*8-1:0]               dma_awlen,
    output logic [PORT_COUNT*MAX_CHANNELS-1:0]                 dma_awvalid,
    input  logic [PORT_COUNT*MAX_CHANNELS-1:0]                 dma_awready,
    output logic [PORT_COUNT*MAX_CHANNELS*AXI_DATA_WIDTH-1:0]  dma_wdata,
    output logic [PORT_COUNT*MAX_CHANNELS*(AXI_DATA_WIDTH/8)-1:0] dma_wstrb,
    output logic [PORT_COUNT*MAX_CHANNELS-1:0]                 dma_wlast,
    output logic [PORT_COUNT*MAX_CHANNELS-1:0]                 dma_wvalid,
    input  logic [PORT_COUNT*MAX_CHANNELS-1:0]                 dma_wready,
    input  logic [PORT_COUNT*MAX_CHANNELS*2-1:0]               dma_bresp,
    input  logic [PORT_COUNT*MAX_CHANNELS-1:0]                 dma_bvalid,
    output logic [PORT_COUNT*MAX_CHANNELS-1:0]                 dma_bready,

    // Interrupt
    output logic [PORT_COUNT*8-1:0]             eth_intr,

    // Status
    input  logic                                link_status [PORT_COUNT],
    input  logic [1:0]                          link_speed [PORT_COUNT],
    input  logic                                duplex_mode [PORT_COUNT]
);

    // Internal Signals
    logic [PORT_COUNT-1:0]                       mac_tx_clk;
    logic [PORT_COUNT-1:0]                       mac_rx_clk;
    logic [PORT_COUNT-1:0]                       mac_tx_en;
    logic [PORT_COUNT-1:0]                       mac_tx_err;
    logic [PORT_COUNT*7:0]                       mac_tx_data;
    logic [PORT_COUNT-1:0]                       mac_rx_dv;
    logic [PORT_COUNT-1:0]                       mac_rx_err;
    logic [PORT_COUNT*7:0]                       mac_rx_data;
    logic [PORT_COUNT-1:0]                       mac_col;
    logic [PORT_COUNT-1:0]                       mac_crs;

    // DMA Channel Signals
    logic [MAX_CHANNELS-1:0]                     dma_tx_req;
    logic [MAX_CHANNELS-1:0]                     dma_tx_done;
    logic [MAX_CHANNELS-1:0]                     dma_rx_req;
    logic [MAX_CHANNELS-1:0]                     dma_rx_done;
    logic [MAX_CHANNELS-1:0]                     dma_err;

    // Statistics
    logic [PORT_COUNT-1:0]                       stats_tx_bytes [8];
    logic [PORT_COUNT-1:0]                       stats_rx_bytes [8];
    logic [PORT_COUNT-1:0]                       stats_tx_pkts [8];
    logic [PORT_COUNT-1:0]                       stats_rx_pkts [8];
    logic [PORT_COUNT-1:0]                       stats_tx_errors [8];
    logic [PORT_COUNT-1:0]                       stats_rx_errors [8];

    // Generate MAC Controllers per port
    genvar port_idx;
    generate
        for (port_idx = 0; port_idx < PORT_COUNT; port_idx++) begin : port_gen
            mac_controller #(
                .PORT_ID(port_idx),
                .TSN_ENABLE(TSN_ENABLE)
            ) u_mac (
                .clk_sys(clk_sys),
                .clk_phy(clk_phy),
                .rst_n_sys(rst_n_sys),
                .rst_n_phy(rst_n_phy),
                .tx_axis_tvalid(tx_axis_tvalid[port_idx]),
                .tx_axis_tlast(tx_axis_tlast[port_idx]),
                .tx_axis_tuser(tx_axis_tuser[port_idx*7+:7]),
                .tx_axis_tdata(tx_axis_tdata[port_idx*127+:127]),
                .tx_axis_tready(tx_axis_tready[port_idx]),
                .rx_axis_tvalid(rx_axis_tvalid[port_idx]),
                .rx_axis_tlast(rx_axis_tlast[port_idx]),
                .rx_axis_tuser(rx_axis_tuser[port_idx*7+:7]),
                .rx_axis_tdata(rx_axis_tdata[port_idx*127+:127]),
                .rx_axis_tready(rx_axis_tready[port_idx]),
                .mac_tx_clk(mac_tx_clk[port_idx]),
                .mac_rx_clk(mac_rx_clk[port_idx]),
                .mac_tx_en(mac_tx_en[port_idx]),
                .mac_tx_err(mac_tx_err[port_idx]),
                .mac_tx_data(mac_tx_data[port_idx*7+:7]),
                .mac_rx_dv(mac_rx_dv[port_idx]),
                .mac_rx_err(mac_rx_err[port_idx]),
                .mac_rx_data(mac_rx_data[port_idx*7+:7]),
                .mac_col(mac_col[port_idx]),
                .mac_crs(mac_crs[port_idx]),
                .link_status(link_status[port_idx]),
                .link_speed(link_speed[port_idx]),
                .duplex_mode(duplex_mode[port_idx]),
                .eth_intr(eth_intr[port_idx*8+:8]),
                .stats_tx_bytes(stats_tx_bytes[port_idx]),
                .stats_rx_bytes(stats_rx_bytes[port_idx]),
                .stats_tx_pkts(stats_tx_pkts[port_idx]),
                .stats_rx_pkts(stats_rx_pkts[port_idx]),
                .stats_tx_errors(stats_tx_errors[port_idx]),
                .stats_rx_errors(stats_rx_errors[port_idx])
            );

            phy_interface #(
                .PORT_ID(port_idx)
            ) u_phy_if (
                .clk_sys(clk_sys),
                .clk_phy(clk_phy),
                .rst_n_sys(rst_n_sys),
                .rst_n_phy(rst_n_phy),
                .mac_tx_clk(mac_tx_clk[port_idx]),
                .mac_rx_clk(mac_rx_clk[port_idx]),
                .mac_tx_en(mac_tx_en[port_idx]),
                .mac_tx_err(mac_tx_err[port_idx]),
                .mac_tx_data(mac_tx_data[port_idx*7+:7]),
                .mac_rx_dv(mac_rx_dv[port_idx]),
                .mac_rx_err(mac_rx_err[port_idx]),
                .mac_rx_data(mac_rx_data[port_idx*7+:7]),
                .mac_col(mac_col[port_idx]),
                .mac_crs(mac_crs[port_idx]),
                .phy_tx_clk(phy_tx_clk[port_idx]),
                .phy_rx_clk(phy_rx_clk[port_idx]),
                .phy_tx_en(phy_tx_en[port_idx]),
                .phy_tx_err(phy_tx_err[port_idx]),
                .phy_tx_data(phy_tx_data[port_idx*7+:7]),
                .phy_rx_dv(phy_rx_dv[port_idx]),
                .phy_rx_err(phy_rx_err[port_idx]),
                .phy_rx_data(phy_rx_data[port_idx*7+:7]),
                .phy_col(phy_col[port_idx]),
                .phy_crs(phy_crs[port_idx]),
                .phy_reset_n(phy_reset_n[port_idx]),
                .rgmii_tx_clk(rgmii_tx_clk[port_idx]),
                .rgmii_tx_ctl(rgmii_tx_ctl[port_idx]),
                .rgmii_txd(rgmii_txd[port_idx*4+:4]),
                .rgmii_rx_clk(rgmii_rx_clk[port_idx]),
                .rgmii_rx_ctl(rgmii_rx_ctl[port_idx]),
                .rgmii_rxd(rgmii_rxd[port_idx*4+:4]),
                .xgmii_tx_clk(xgmii_tx_clk[port_idx]),
                .xgmii_tx_ctl(xgmii_tx_ctl[port_idx]),
                .xgmii_txd(xgmii_txd[port_idx*64+:64]),
                .xgmii_rx_clk(xgmii_rx_clk[port_idx]),
                .xgmii_rx_ctl(xgmii_rx_ctl[port_idx]),
                .xgmii_rxd(xgmii_rxd[port_idx*64+:64])
            );
        end
    endgenerate

    // DMA Controllers
    generate
        for (port_idx = 0; port_idx < PORT_COUNT; port_idx++) begin : dma_gen
            for (genvar ch = 0; ch < MAX_CHANNELS; ch++) begin : channel_gen
                dma_controller #(
                    .PORT_ID(port_idx),
                    .CHANNEL_ID(ch),
                    .AXI_DATA_WIDTH(AXI_DATA_WIDTH)
                ) u_dma (
                    .clk_sys(clk_sys),
                    .rst_n_sys(rst_n_sys),
                    .tx_req(dma_tx_req[ch]),
                    .tx_done(dma_tx_done[ch]),
                    .rx_req(dma_rx_req[ch]),
                    .rx_done(dma_rx_done[ch]),
                    .dma_err(dma_err[ch]),
                    .s_axibus_awaddr(dma_awaddr[port_idx*MAX_CHANNELS*AXI_ADDR_WIDTH+ch*AXI_ADDR_WIDTH+:AXI_ADDR_WIDTH]),
                    .s_axibus_awlen(dma_awlen[port_idx*MAX_CHANNELS*8+ch*8+:8]),
                    .s_axibus_awvalid(dma_awvalid[port_idx*MAX_CHANNELS+ch]),
                    .s_axibus_awready(dma_awready[port_idx*MAX_CHANNELS+ch]),
                    .s_axibus_wdata(dma_wdata[port_idx*MAX_CHANNELS*AXI_DATA_WIDTH+ch*AXI_DATA_WIDTH+:AXI_DATA_WIDTH]),
                    .s_axibus_wstrb(dma_wstrb[port_idx*MAX_CHANNELS*(AXI_DATA_WIDTH/8)+ch*(AXI_DATA_WIDTH/8)+:(AXI_DATA_WIDTH/8)]),
                    .s_axibus_wlast(dma_wlast[port_idx*MAX_CHANNELS+ch]),
                    .s_axibus_wvalid(dma_wvalid[port_idx*MAX_CHANNELS+ch]),
                    .s_axibus_wready(dma_wready[port_idx*MAX_CHANNELS+ch]),
                    .s_axibus_bresp(dma_bresp[port_idx*MAX_CHANNELS*2+ch*2+:2]),
                    .s_axibus_bvalid(dma_bvalid[port_idx*MAX_CHANNELS+ch]),
                    .s_axibus_bready(dma_bready[port_idx*MAX_CHANNELS+ch]),
                    .s_axibus_araddr(dma_araddr[port_idx*MAX_CHANNELS*AXI_ADDR_WIDTH+ch*AXI_ADDR_WIDTH+:AXI_ADDR_WIDTH]),
                    .s_axibus_arlen(dma_arlen[port_idx*MAX_CHANNELS*4+ch*4+:4]),
                    .s_axibus_arvalid(dma_arvalid[port_idx*MAX_CHANNELS+ch]),
                    .s_axibus_arready(dma_arready[port_idx*MAX_CHANNELS+ch]),
                    .s_axibus_rdata(dma_rdata[port_idx*MAX_CHANNELS*AXI_DATA_WIDTH+ch*AXI_DATA_WIDTH+:AXI_DATA_WIDTH]),
                    .s_axibus_rvalid(dma_rvalid[port_idx*MAX_CHANNELS+ch]),
                    .s_axibus_rlast(dma_rlast[port_idx*MAX_CHANNELS+ch])
                );
            end
        end
    endgenerate

    // Frame Preprocessor
    generate
        for (port_idx = 0; port_idx < PORT_COUNT; port_idx++) begin : preproc_gen
            frame_preprocessor #(
                .PORT_ID(port_idx)
            ) u_frame_preproc (
                .clk_sys(clk_sys),
                .rst_n_sys(rst_n_sys),
                .tx_axis_tvalid(tx_axis_tvalid[port_idx]),
                .tx_axis_tlast(tx_axis_tlast[port_idx]),
                .tx_axis_tuser(tx_axis_tuser[port_idx*7+:7]),
                .tx_axis_tdata(tx_axis_tdata[port_idx*127+:127]),
                .tx_axis_tready(tx_axis_tready[port_idx]),
                .rx_axis_tvalid(rx_axis_tvalid[port_idx]),
                .rx_axis_tlast(rx_axis_tlast[port_idx]),
                .rx_axis_tuser(rx_axis_tuser[port_idx*7+:7]),
                .rx_axis_tdata(rx_axis_tdata[port_idx*127+:127]),
                .rx_axis_tready(rx_axis_tready[port_idx]),
                .mac_tx_clk(mac_tx_clk[port_idx]),
                .mac_rx_clk(mac_rx_clk[port_idx]),
                .mac_tx_en(mac_tx_en[port_idx]),
                .mac_tx_err(mac_tx_err[port_idx]),
                .mac_tx_data(mac_tx_data[port_idx*7+:7]),
                .mac_rx_dv(mac_rx_dv[port_idx]),
                .mac_rx_err(mac_rx_err[port_idx]),
                .mac_rx_data(mac_rx_data[port_idx*7+:7]),
                .tsn_enable(TSN_ENABLE),
                .vlan_detect(vlan_detect[port_idx]),
                .tsm_insert(tsm_insert[port_idx]),
                .error_frame(error_frame[port_idx])
            );
        end
    endgenerate

    // AXI Slave Interface for Management
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            s_axibus_awready <= 1'b1;
            s_axibus_wready <= 1'b0;
            s_axibus_bvalid <= 1'b0;
            s_axibus_arready <= 1'b1;
            s_axibus_rvalid <= 1'b0;
        end else begin
            s_axibus_awready <= !s_axibus_awvalid;
            s_axibus_wready <= (s_axibus_awvalid && s_axibus_awready) && !s_axibus_wvalid;

            if (s_axibus_awvalid && s_axibus_awready) begin
                s_axibus_awready <= 1'b0;
                s_axibus_wready <= 1'b1;
            end

            if (s_axibus_wvalid && s_axibus_wready && s_axibus_wlast) begin
                s_axibus_bvalid <= 1'b1;
                s_axibus_bresp <= '0;
            end

            if (s_axibus_bvalid && s_axibus_bready) begin
                s_axibus_bvalid <= 1'b0;
            end

            s_axibus_arready <= !s_axibus_arvalid;

            if (s_axibus_arvalid && s_axibus_arready) begin
                s_axibus_arready <= 1'b0;
                case (s_axibus_araddr[11:8])
                    4'h0: s_axibus_rdata <= {link_status, link_speed, duplex_mode};
                    4'h1: s_axibus_rdata <= stats_tx_bytes;
                    4'h2: s_axibus_rdata <= stats_rx_bytes;
                    4'h3: s_axibus_rdata <= stats_tx_pkts;
                    4'h4: s_axibus_rdata <= stats_rx_pkts;
                    default: s_axibus_rdata <= '0;
                endcase
                s_axibus_rvalid <= 1'b1;
            end else begin
                s_axibus_rvalid <= 1'b0;
            end
        end
    end

endmodule
