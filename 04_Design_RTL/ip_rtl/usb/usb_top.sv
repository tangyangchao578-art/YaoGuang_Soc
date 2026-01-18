//-----------------------------------------------------------------------------
// File: usb_top.sv
// Description: USB 3.2 Gen2 Controller Top Level
// Author: YaoGuang SoC Team
// Date: 2026-01-19
//-----------------------------------------------------------------------------

`timescale 1ps/1ps

module usb_top #(
    parameter PORT_COUNT = 4,
    parameter MAX_EPS = 16,
    parameter AXI_DATA_WIDTH = 128,
    parameter AXI_ADDR_WIDTH = 48
) (
    input  logic                                clk_sys,
    input  logic                                clk_phy,
    input  logic                                rst_n_sys,
    input  logic                                rst_n_phy,

    // AXI4 Slave Interface
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

    // USB PHY Interface
    input  logic [PORT_COUNT-1:0]               usb2_rx_dp,
    input  logic [PORT_COUNT-1:0]               usb2_rx_dn,
    output logic [PORT_COUNT-1:0]               usb2_tx_dp,
    output logic [PORT_COUNT-1:0]               usb2_tx_dn,
    output logic [PORT_COUNT-1:0]               usb2_tx_oe,
    input  logic [PORT_COUNT-1:0]               usb2_rx_valid,
    output logic [PORT_COUNT-1:0]               usb3_tx_p,
    output logic [PORT_COUNT-1:0]               usb3_tx_n,
    input  logic [PORT_COUNT-1:0]               usb3_rx_p,
    input  logic [PORT_COUNT-1:0]               usb3_rx_n,
    output logic [PORT_COUNT-1:0]               usb3_tx_elec_idle,
    output logic                                ref_clk_p,
    output logic                                ref_clk_n,
    input  logic                                phy_ready,
    input  logic                                phy_status,

    // Interrupt
    output logic [PORT_COUNT*4-1:0]             usb_intr,
    output logic                                usb_overcurrent,

    // Power Management
    input  logic                                runtime_suspend,
    output logic                                runtime_resume,
    input  logic                                global_power_enable
);

    // Internal Signals
    logic [15:0]                                dev_addr;
    logic                                        device_configured;
    logic [PORT_COUNT-1:0]                       port_connected;
    logic [PORT_COUNT-1:0]                       port_enabled;
    logic [PORT_COUNT-1:0]                       port_speed;
    logic [PORT_COUNT-1:0]                       port_overcurrent;

    // AXI Interconnect
    logic [PORT_COUNT*AXI_ADDR_WIDTH-1:0]        ep_axibus_awaddr;
    logic [PORT_COUNT*4-1:0]                     ep_axibus_awid;
    logic [PORT_COUNT*8-1:0]                     ep_axibus_awlen;
    logic [PORT_COUNT*3-1:0]                     ep_axibus_awsize;
    logic [PORT_COUNT*2-1:0]                     ep_axibus_awburst;
    logic [PORT_COUNT-1:0]                       ep_axibus_awvalid;
    logic [PORT_COUNT-1:0]                       ep_axibus_awready;
    logic [PORT_COUNT*AXI_DATA_WIDTH-1:0]        ep_axibus_wdata;
    logic [PORT_COUNT*(AXI_DATA_WIDTH/8)-1:0]    ep_axibus_wstrb;
    logic [PORT_COUNT-1:0]                       ep_axibus_wlast;
    logic [PORT_COUNT-1:0]                       ep_axibus_wvalid;
    logic [PORT_COUNT-1:0]                       ep_axibus_wready;
    logic [PORT_COUNT*2-1:0]                     ep_axibus_bresp;
    logic [PORT_COUNT-1:0]                       ep_axibus_bvalid;
    logic [PORT_COUNT-1:0]                       ep_axibus_bready;
    logic [PORT_COUNT*AXI_ADDR_WIDTH-1:0]        ep_axibus_araddr;
    logic [PORT_COUNT*4-1:0]                     ep_axibus_arid;
    logic [PORT_COUNT*8-1:0]                     ep_axibus_arlen;
    logic [PORT_COUNT*3-1:0]                     ep_axibus_arsize;
    logic [PORT_COUNT*2-1:0]                     ep_axibus_arburst;
    logic [PORT_COUNT-1:0]                       ep_axibus_arvalid;
    logic [PORT_COUNT-1:0]                       ep_axibus_arready;
    logic [PORT_COUNT*AXI_DATA_WIDTH-1:0]        ep_axibus_rdata;
    logic [PORT_COUNT*2-1:0]                     ep_axibus_rresp;
    logic [PORT_COUNT-1:0]                       ep_axibus_rlast;
    logic [PORT_COUNT-1:0]                       ep_axibus_rvalid;
    logic [PORT_COUNT-1:0]                       ep_axibus_rready;

    // USB Protocol Signals
    logic [PORT_COUNT-1:0]                       usb2_rx_data;
    logic [PORT_COUNT-1:0]                       usb2_tx_data;
    logic [PORT_COUNT-1:0]                       usb2_tx_se0;
    logic [PORT_COUNT-1:0]                       usb2_rx_valid_reg;
    logic [PORT_COUNT*10-1:0]                    usb3_tx_data;
    logic [PORT_COUNT*10-1:0]                    usb3_rx_data;
    logic [PORT_COUNT-1:0]                       usb3_rx_valid;
    logic [PORT_COUNT-1:0]                       usb3_rx_header_valid;

    // USB 3.2 Controller Instance
    generate
        for (genvar i = 0; i < PORT_COUNT; i++) begin : port_gen
            usb_host_device_controller #(
                .PORT_ID(i),
                .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
                .MAX_EPS(MAX_EPS)
            ) u_controller (
                .clk_sys(clk_sys),
                .clk_phy(clk_phy),
                .rst_n_sys(rst_n_sys),
                .rst_n_phy(rst_n_phy),
                .dev_addr(dev_addr),
                .device_configured(device_configured),
                .port_connected(port_connected[i]),
                .port_enabled(port_enabled[i]),
                .port_speed(port_speed[i]),
                .port_overcurrent(port_overcurrent[i]),
                .s_axibus_awaddr(ep_axibus_awaddr[i*AXI_ADDR_WIDTH+:AXI_ADDR_WIDTH]),
                .s_axibus_awid(ep_axibus_awid[i*4+:4]),
                .s_axibus_awlen(ep_axibus_awlen[i*8+:8]),
                .s_axibus_awsize(ep_axibus_awsize[i*3+:3]),
                .s_axibus_awburst(ep_axibus_awburst[i*2+:2]),
                .s_axibus_awvalid(ep_axibus_awvalid[i]),
                .s_axibus_awready(ep_axibus_awready[i]),
                .s_axibus_wdata(ep_axibus_wdata[i*AXI_DATA_WIDTH+:AXI_DATA_WIDTH]),
                .s_axibus_wstrb(ep_axibus_wstrb[i*(AXI_DATA_WIDTH/8)+:(AXI_DATA_WIDTH/8)]),
                .s_axibus_wlast(ep_axibus_wlast[i]),
                .s_axibus_wvalid(ep_axibus_wvalid[i]),
                .s_axibus_wready(ep_axibus_wready[i]),
                .s_axibus_bresp(ep_axibus_bresp[i*2+:2]),
                .s_axibus_bvalid(ep_axibus_bvalid[i]),
                .s_axibus_bready(ep_axibus_bready[i]),
                .s_axibus_araddr(ep_axibus_araddr[i*AXI_ADDR_WIDTH+:AXI_ADDR_WIDTH]),
                .s_axibus_arid(ep_axibus_arid[i*4+:4]),
                .s_axibus_arlen(ep_axibus_arlen[i*8+:8]),
                .s_axibus_arsize(ep_axibus_arsize[i*3+:3]),
                .s_axibus_arburst(ep_axibus_arburst[i*2+:2]),
                .s_axibus_arvalid(ep_axibus_arvalid[i]),
                .s_axibus_arready(ep_axibus_arready[i]),
                .s_axibus_rdata(ep_axibus_rdata[i*AXI_DATA_WIDTH+:AXI_DATA_WIDTH]),
                .s_axibus_rresp(ep_axibus_rresp[i*2+:2]),
                .s_axibus_rlast(ep_axibus_rlast[i]),
                .s_axibus_rvalid(ep_axibus_rvalid[i]),
                .s_axibus_rready(ep_axibus_rready[i]),
                .usb2_rx_dp(usb2_rx_dp[i]),
                .usb2_rx_dn(usb2_rx_dn[i]),
                .usb2_tx_dp(usb2_tx_dp[i]),
                .usb2_tx_dn(usb2_tx_dn[i]),
                .usb2_tx_oe(usb2_tx_oe[i]),
                .usb2_rx_valid(usb2_rx_valid_reg[i]),
                .usb3_tx_p(usb3_tx_p[i]),
                .usb3_tx_n(usb3_tx_n[i]),
                .usb3_rx_p(usb3_rx_p[i]),
                .usb3_rx_n(usb3_rx_n[i]),
                .usb3_tx_elec_idle(usb3_tx_elec_idle[i]),
                .usb3_rx_data(usb3_rx_data[i*10+:10]),
                .usb3_rx_valid(usb3_rx_valid[i]),
                .usb3_rx_header_valid(usb3_rx_header_valid[i]),
                .usb_intr(usb_intr[i*4+:4]),
                .usb_overcurrent(usb_overcurrent[i]),
                .runtime_suspend(runtime_suspend),
                .runtime_resume(runtime_resume),
                .global_power_enable(global_power_enable)
            );
        end
    endgenerate

    // USB 2.0 PHY
    generate
        for (genvar i = 0; i < PORT_COUNT; i++) begin : usb2_phy_gen
            usb_20_phy #(
                .PORT_ID(i)
            ) u_usb20_phy (
                .clk_phy(clk_phy),
                .rst_n_phy(rst_n_phy),
                .tx_data(usb2_tx_data[i]),
                .tx_se0(usb2_tx_se0[i]),
                .tx_oe(usb2_tx_oe[i]),
                .rx_dp(usb2_rx_dp[i]),
                .rx_dn(usb2_rx_dn[i]),
                .rx_valid(usb2_rx_valid_reg[i]),
                .rx_data(usb2_rx_data[i]),
                .phy_ready(phy_ready),
                .phy_status(phy_status[i])
            );
        end
    endgenerate

    // USB 3.0 PHY Interface
    generate
        for (genvar i = 0; i < PORT_COUNT; i++) begin : usb3_phy_gen
            usb_30_phy_if #(
                .PORT_ID(i)
            ) u_usb30_phy_if (
                .clk_phy(clk_phy),
                .rst_n_phy(rst_n_phy),
                .tx_data(usb3_tx_data[i*10+:10]),
                .tx_valid(usb3_tx_valid),
                .tx_ready(usb3_tx_ready),
                .tx_elec_idle(usb3_tx_elec_idle[i]),
                .rx_data(usb3_rx_data[i*10+:10]),
                .rx_valid(usb3_rx_valid[i]),
                .rx_header_valid(usb3_rx_header_valid[i]),
                .rx_ready(usb3_rx_ready),
                .phy_p(usb3_tx_p[i]),
                .phy_n(usb3_tx_n[i]),
                .phy_rx_p(usb3_rx_p[i]),
                .phy_rx_n(usb3_rx_n[i]),
                .ref_clk_p(ref_clk_p),
                .ref_clk_n(ref_clk_n)
            );
        end
    endgenerate

    // Device Address and Configuration
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            dev_addr <= 16'h0000;
            device_configured <= 1'b0;
            port_enabled <= '0;
            port_speed <= '0;
        end else begin
            if (s_axibus_awvalid && s_axibus_awready) begin
                if (s_axibus_awaddr[11:8] == 4'h0) begin
                    dev_addr <= s_axibus_wdata[15:0];
                end
                if (s_axibus_awaddr[11:8] == 4'h1) begin
                    device_configured <= s_axibus_wdata[0];
                    port_enabled <= s_axibus_wdata[7:4];
                    port_speed <= s_axibus_wdata[15:12];
                end
            end
        end
    end

    // Port Connection Management
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            port_connected <= '0;
            port_overcurrent <= '0;
        end else begin
            for (int i = 0; i < PORT_COUNT; i++) begin
                if (phy_status[i*2]) begin
                    port_connected[i] <= 1'b1;
                end
                if (usb_overcurrent[i]) begin
                    port_overcurrent[i] <= 1'b1;
                end
            end
        end
    end

endmodule
