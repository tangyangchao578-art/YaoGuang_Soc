// -----------------------------------------------------------------------------
// File: display_top.sv
// Description: Display Subsystem Top-level Module
// Author: YaoGuang SoC Design Team
// Date: 2026-01-18
// -----------------------------------------------------------------------------

`timescale 1ns/1ps

module display_top #(
    parameter integer AXI_DATA_WIDTH = 64,
    parameter integer AXI_ADDR_WIDTH = 32,
    parameter integer NUM_CHANNELS   = 3
) (
    // System Interface
    input  logic                                    clk_sys,
    input  logic                                    rst_n,
    output logic                                    int_display,

    // NoC Slave Interface (Configuration)
    input  logic [AXI_ADDR_WIDTH-1:0]              s_awaddr,
    input  logic                                    s_awvalid,
    output logic                                    s_awready,
    input  logic [AXI_DATA_WIDTH-1:0]              s_wdata,
    input  logic [AXI_DATA_WIDTH/8-1:0]            s_wstrb,
    input  logic                                    s_wvalid,
    output logic                                    s_wready,
    output logic [1:0]                             s_bresp,
    output logic                                    s_bvalid,
    input  logic                                    s_bready,
    input  logic [AXI_ADDR_WIDTH-1:0]              s_araddr,
    input  logic                                    s_arvalid,
    output logic                                    s_arready,
    output logic [AXI_DATA_WIDTH-1:0]              s_rdata,
    output logic [1:0]                             s_rresp,
    output logic                                    s_rvalid,
    input  logic                                    s_rready,

    // AXI Master Interface (Framebuffer Read)
    output logic [AXI_ADDR_WIDTH-1:0]              m_araddr,
    output logic [7:0]                             m_arlen,
    output logic [2:0]                             m_arsize,
    output logic [1:0]                             m_arburst,
    output logic                                    m_arvalid,
    input  logic                                    m_arready,
    input  logic [AXI_DATA_WIDTH-1:0]              m_rdata,
    input  logic [1:0]                             m_rresp,
    input  logic                                    m_rvalid,
    output logic                                    m_rready,

    // HDMI 2.1 Interface
    output logic                                    hdmi_tx_clk_p,
    output logic                                    hdmi_tx_clk_n,
    output logic [2:0]                             hdmi_tx_data_p,
    output logic [2:0]                             hdmi_tx_data_n,
    input  logic                                   hdmi_hpd,
    output logic                                   hdmi_cec,

    // DisplayPort 1.4a Interface
    output logic [3:0]                             dp_tx_data_p,
    output logic [3:0]                             dp_tx_data_n,
    output logic                                    dp_tx_clk_p,
    output logic                                    dp_tx_clk_n,
    input  logic                                   dp_hpd,
    inout  logic                                   dp_aux_p,
    inout  logic                                   dp_aux_n,

    // MIPI DSI-2 Interface
    output logic                                    dsi_clk_p,
    output logic                                    dsi_clk_n,
    output logic [3:0]                             dsi_data_p,
    output logic [3:0]                             dsi_data_n,
    input  logic                                   dsi_te,
    output logic                                   dsi_rst_n
);

    // -------------------------------------------------------------------------
    // Internal Signals
    // -------------------------------------------------------------------------
    logic [7:0]                                    pixel_clk;
    logic                                          rst_pixel_n;
    logic                                          pixel_clk_locked;

    logic                                          frame_start;
    logic                                          line_start;
    logic                                          pixel_valid;
    logic [31:0]                                   pixel_data_r;
    logic [31:0]                                   pixel_data_g;
    logic [31:0]                                   pixel_data_b;
    logic                                          pixel_de;
    logic                                          pixel_hsync;
    logic                                          pixel_vsync;

    logic                                          disp_enable;
    logic [1:0]                                    output_sel;

    logic [AXI_ADDR_WIDTH-1:0]                     fb_base_addr;
    logic [31:0]                                   fb_stride;
    logic [7:0]                                    pixel_format;

    // APB to Register Bridge
    logic [31:0]                                   reg_rdata;
    logic                                          reg_ready;

    // -------------------------------------------------------------------------
    // Clock and Reset Management
    // -------------------------------------------------------------------------
    display_clk_rst display_clk_rst_inst (
        .clk_sys            (clk_sys),
        .rst_n              (rst_n),
        .pixel_clk          (pixel_clk),
        .rst_pixel_n        (rst_pixel_n),
        .clk_locked         (pixel_clk_locked)
    );

    // -------------------------------------------------------------------------
    // Register Map
    // -------------------------------------------------------------------------
    display_reg_map #(
        .ADDR_WIDTH         (AXI_ADDR_WIDTH)
    ) display_reg_map_inst (
        .clk                (clk_sys),
        .rst_n              (rst_n),
        .s_awaddr           (s_awaddr),
        .s_awvalid          (s_awvalid),
        .s_awready          (s_awready),
        .s_wdata            (s_wdata),
        .s_wstrb            (s_wstrb),
        .s_wvalid           (s_wvalid),
        .s_wready           (s_wready),
        .s_bresp            (s_bresp),
        .s_bvalid           (s_bvalid),
        .s_bready           (s_bready),
        .s_araddr           (s_araddr),
        .s_arvalid          (s_arvalid),
        .s_arready          (s_arready),
        .s_rdata            (s_rdata),
        .s_rresp            (s_rresp),
        .s_rvalid           (s_rvalid),
        .s_rready           (s_rready),
        .reg_rdata          (reg_rdata),
        .reg_ready          (reg_ready),
        .disp_enable        (disp_enable),
        .output_sel         (output_sel),
        .fb_base_addr       (fb_base_addr),
        .fb_stride          (fb_stride),
        .pixel_format       (pixel_format),
        .int_display        (int_display)
    );

    // -------------------------------------------------------------------------
    // Display Engine
    // -------------------------------------------------------------------------
    display_engine #(
        .NUM_CHANNELS       (NUM_CHANNELS)
    ) display_engine_inst (
        .pixel_clk          (pixel_clk),
        .rst_n              (rst_pixel_n),
        .disp_enable        (disp_enable),
        .output_sel         (output_sel),
        .fb_base_addr       (fb_base_addr),
        .fb_stride          (fb_stride),
        .pixel_format       (pixel_format),
        .frame_start        (frame_start),
        .line_start         (line_start),
        .pixel_valid        (pixel_valid),
        .pixel_data_r       (pixel_data_r),
        .pixel_data_g       (pixel_data_g),
        .pixel_data_b       (pixel_data_b),
        .pixel_de           (pixel_de),
        .pixel_hsync        (pixel_hsync),
        .pixel_vsync        (pixel_vsync),
        .m_araddr           (m_araddr),
        .m_arlen            (m_arlen),
        .m_arsize           (m_arsize),
        .m_arburst          (m_arburst),
        .m_arvalid          (m_arvalid),
        .m_arready          (m_arready),
        .m_rdata            (m_rdata),
        .m_rresp            (m_rresp),
        .m_rvalid           (m_rvalid),
        .m_rready           (m_rready)
    );

    // -------------------------------------------------------------------------
    // Framebuffer Reader
    // -------------------------------------------------------------------------
    framebuffer_reader #(
        .AXI_DATA_WIDTH     (AXI_DATA_WIDTH),
        .AXI_ADDR_WIDTH     (AXI_ADDR_WIDTH)
    ) framebuffer_reader_inst (
        .pixel_clk          (pixel_clk),
        .rst_n              (rst_pixel_n),
        .frame_start        (frame_start),
        .fb_base_addr       (fb_base_addr),
        .fb_stride          (fb_stride),
        .pixel_format       (pixel_format),
        .pixel_valid        (pixel_valid),
        .pixel_data_r       (pixel_data_r),
        .pixel_data_g       (pixel_data_g),
        .pixel_data_b       (pixel_data_b)
    );

    // -------------------------------------------------------------------------
    // Color Processing Pipeline
    // -------------------------------------------------------------------------
    color_processing #(
        .DATA_WIDTH         (12)
    ) color_processing_inst (
        .pixel_clk          (pixel_clk),
        .rst_n              (rst_pixel_n),
        .pixel_valid        (pixel_valid),
        .pixel_data_r       (pixel_data_r[11:0]),
        .pixel_data_g       (pixel_data_g[11:0]),
        .pixel_data_b       (pixel_data_b[11:0]),
        .pixel_de           (pixel_de),
        .pixel_hsync        (pixel_hsync),
        .pixel_vsync        (pixel_vsync),
        .out_valid          (pixel_valid),
        .out_data_r         (pixel_data_r[11:0]),
        .out_data_g         (pixel_data_g[11:0]),
        .out_data_b         (pixel_data_b[11:0]),
        .out_de             (pixel_de),
        .out_hsync          (pixel_hsync),
        .out_vsync          (pixel_vsync)
    );

    // -------------------------------------------------------------------------
    // HDMI 2.1 Transmitter
    // -------------------------------------------------------------------------
    hdmi_tx #(
        .DATA_WIDTH         (12)
    ) hdmi_tx_inst (
        .pixel_clk          (pixel_clk),
        .rst_n              (rst_pixel_n),
        .pixel_valid        (pixel_valid),
        .pixel_data_r       (pixel_data_r[11:0]),
        .pixel_data_g       (pixel_data_g[11:0]),
        .pixel_data_b       (pixel_data_b[11:0]),
        .pixel_de           (pixel_de),
        .pixel_hsync        (pixel_hsync),
        .pixel_vsync        (pixel_vsync),
        .hdmi_tx_clk_p      (hdmi_tx_clk_p),
        .hdmi_tx_clk_n      (hdmi_tx_clk_n),
        .hdmi_tx_data_p     (hdmi_tx_data_p),
        .hdmi_tx_data_n     (hdmi_tx_data_n),
        .hdmi_hpd           (hdmi_hpd),
        .hdmi_cec           (hdmi_cec)
    );

    // -------------------------------------------------------------------------
    // DisplayPort 1.4a Transmitter
    // -------------------------------------------------------------------------
    dp_tx dp_tx_inst (
        .pixel_clk          (pixel_clk),
        .rst_n              (rst_pixel_n),
        .pixel_valid        (pixel_valid),
        .pixel_data_r       (pixel_data_r[11:0]),
        .pixel_data_g       (pixel_data_g[11:0]),
        .pixel_data_b       (pixel_data_b[11:0]),
        .pixel_de           (pixel_de),
        .pixel_hsync        (pixel_hsync),
        .pixel_vsync        (pixel_vsync),
        .dp_tx_data_p       (dp_tx_data_p),
        .dp_tx_data_n       (dp_tx_data_n),
        .dp_tx_clk_p        (dp_tx_clk_p),
        .dp_tx_clk_n        (dp_tx_clk_n),
        .dp_hpd             (dp_hpd),
        .dp_aux_p           (dp_aux_p),
        .dp_aux_n           (dp_aux_n)
    );

    // -------------------------------------------------------------------------
    // MIPI DSI-2 Transmitter
    // -------------------------------------------------------------------------
    mipi_dsi_tx mipi_dsi_tx_inst (
        .pixel_clk          (pixel_clk),
        .rst_n              (rst_pixel_n),
        .pixel_valid        (pixel_valid),
        .pixel_data_r       (pixel_data_r[11:0]),
        .pixel_data_g       (pixel_data_g[11:0]),
        .pixel_data_b       (pixel_data_b[11:0]),
        .pixel_de           (pixel_de),
        .pixel_hsync        (pixel_hsync),
        .pixel_vsync        (pixel_vsync),
        .dsi_clk_p          (dsi_clk_p),
        .dsi_clk_n          (dsi_clk_n),
        .dsi_data_p         (dsi_data_p),
        .dsi_data_n         (dsi_data_n),
        .dsi_te             (dsi_te),
        .dsi_rst_n          (dsi_rst_n)
    );

endmodule
