// Copyright (c) 2026 YaoGuang SoC Project
// All rights reserved

// Audio Top Level Module
// Revision: 1.0
// Date: 2026-01-18

`timescale 1ns/1ps

module audio_top (
    // APB Interface
    input  wire         pclk,
    input  wire         prst_n,
    input  wire [11:0]  paddr,
    input  wire         pwrite,
    input  wire [31:0]  pwdata,
    output wire [31:0]  prdata,
    input  wire         psel,
    input  wire         penable,
    output wire         pready,

    // AXI-Stream Interface (TX)
    input  wire         tx_axis_aclk,
    input  wire         tx_axis_rst_n,
    output wire [63:0]  tx_axis_tdata,
    output wire         tx_axis_tvalid,
    input  wire         tx_axis_tready,
    output wire [7:0]   tx_axis_tkeep,
    output wire         tx_axis_tlast,

    // AXI-Stream Interface (RX)
    input  wire         rx_axis_aclk,
    input  wire         rx_axis_rst_n,
    input  wire [63:0]  rx_axis_tdata,
    input  wire         rx_axis_tvalid,
    output wire         rx_axis_tready,
    input  wire [7:0]   rx_axis_tkeep,
    input  wire         rx_axis_tlast,

    // I2S Interface
    input  wire         i2s_bclk_i,
    output wire         i2s_bclk_o,
    inout  wire         i2s_bclk_t,
    input  wire         i2s_lrclk_i,
    output wire         i2s_lrclk_o,
    inout  wire         i2s_lrclk_t,
    output wire         i2s_dout,
    input  wire         i2s_din,
    output wire         i2s_mclk,

    // TDM Interface
    input  wire         tdm_bclk_i,
    output wire         tdm_bclk_o,
    inout  wire         tdm_bclk_t,
    input  wire         tdm_fs_i,
    output wire         tdm_fs_o,
    inout  wire         tdm_fs_t,
    output wire [15:0]  tdm_dout,
    input  wire [15:0]  tdm_din,

    // PDM Interface
    input  wire         pdm_clk,
    input  wire [1:0]   pdm_din,
    output wire         pdm_lrsel,

    // SPDIF Interface
    input  wire         spdif_rx,
    output wire         spdif_tx,

    // Interrupt
    output wire         irq
);

    // Parameters
    localparam [31:0] AUDIO_VERSION = 32'h00010000;

    // Internal Signals
    wire [31:0] reg_prdata;
    wire        reg_pready;
    wire        i2s_enable;
    wire        tdm_enable;
    wire        pdm_enable;
    wire        spdif_enable;
    wire        dsp_enable;
    wire        volume_enable;
    wire        src_enable;
    wire        eq_enable;
    wire        drc_enable;

    wire [31:0] i2s_dout_data;
    wire [31:0] i2s_din_data;
    wire        i2s_dout_valid;
    wire        i2s_din_valid;

    wire [31:0] tdm_dout_data;
    wire [31:0] tdm_din_data;
    wire        tdm_dout_valid;
    wire        tdm_din_valid;

    wire [31:0] pdm_dout_data;
    wire        pdm_dout_valid;

    wire [31:0] spdif_dout_data;
    wire [31:0] spdif_din_data;
    wire        spdif_dout_valid;
    wire        spdif_din_valid;

    wire [31:0] dsp_input_data;
    wire        dsp_input_valid;
    wire [31:0] dsp_output_data;
    wire        dsp_output_valid;

    wire [31:0] volume_data_in;
    wire        volume_valid_in;
    wire [31:0] volume_data_out;
    wire        volume_valid_out;

    wire [31:0] src_data_in;
    wire        src_valid_in;
    wire [31:0] src_data_out;
    wire        src_valid_out;

    // APB Register File
    audio_regfile u_regfile (
        .pclk           (pclk),
        .prst_n         (prst_n),
        .paddr          (paddr),
        .pwrite         (pwrite),
        .pwdata         (pwdata),
        .prdata         (reg_prdata),
        .psel           (psel),
        .penable        (penable),
        .pready         (reg_pready),

        .version        (AUDIO_VERSION),

        .i2s_enable     (i2s_enable),
        .tdm_enable     (tdm_enable),
        .pdm_enable     (pdm_enable),
        .spdif_enable   (spdif_enable),
        .dsp_enable     (dsp_enable),
        .volume_enable  (volume_enable),
        .src_enable     (src_enable),
        .eq_enable      (eq_enable),
        .drc_enable     (drc_enable),

        .irq            (irq)
    );

    // I2S     (drc Controller
    i2s_controller #(
        .CHANNEL_NUM    (2)
    ) u_i2s_controller (
        .clk            (pclk),
        .rst_n          (prst_n),
        .enable         (i2s_enable),

        .bclk_i         (i2s_bclk_i),
        .bclk_o         (i2s_bclk_o),
        .bclk_t         (i2s_bclk_t),
        .lrclk_i        (i2s_lrclk_i),
        .lrclk_o        (i2s_lrclk_o),
        .lrclk_t        (i2s_lrclk_t),
        .dout           (i2s_dout),
        .din            (i2s_din),
        .mclk           (i2s_mclk),

        .pcm_dout       (i2s_dout_data),
        .pcm_dout_valid (i2s_dout_valid),
        .pcm_din        (i2s_din_data),
        .pcm_din_valid  (i2s_din_valid)
    );

    // TDM Controller
    tdm_controller #(
        .CHANNEL_NUM    (8),
        .SLOT_WIDTH     (16)
    ) u_tdm_controller (
        .clk            (pclk),
        .rst_n          (prst_n),
        .enable         (tdm_enable),

        .bclk_i         (tdm_bclk_i),
        .bclk_o         (tdm_bclk_o),
        .bclk_t         (tdm_bclk_t),
        .fs_i           (tdm_fs_i),
        .fs_o           (tdm_fs_o),
        .fs_t           (tdm_fs_t),
        .dout           (tdm_dout),
        .din            (tdm_din),

        .pcm_dout       (tdm_dout_data),
        .pcm_dout_valid (tdm_dout_valid),
        .pcm_din        (tdm_din_data),
        .pcm_din_valid  (tdm_din_valid)
    );

    // PDM Controller
    pdm_controller #(
        .CHANNEL_NUM    (2)
    ) u_pdm_controller (
        .clk            (pclk),
        .rst_n          (prst_n),
        .enable         (pdm_enable),

        .pdm_clk        (pdm_clk),
        .pdm_din        (pdm_din),
        .lrsel          (pdm_lrsel),

        .pcm_dout       (pdm_dout_data),
        .pcm_dout_valid (pdm_dout_valid)
    );

    // SPDIF Controller
    spdif_controller u_spdif_controller (
        .clk            (pclk),
        .rst_n          (prst_n),
        .enable         (spdif_enable),

        .spdif_rx       (spdif_rx),
        .spdif_tx       (spdif_tx),

        .pcm_dout       (spdif_dout_data),
        .pcm_dout_valid (spdif_dout_valid),
        .pcm_din        (spdif_din_data),
        .pcm_din_valid  (spdif_din_valid)
    );

    // Audio DSP
    audio_dsp #(
        .IRAM_SIZE      (4096),
        .DRAM_SIZE      (16384)
    ) u_audio_dsp (
        .clk            (pclk),
        .rst_n          (prst_n),
        .enable         (dsp_enable),

        .pcm_din        (dsp_input_data),
        .pcm_din_valid  (dsp_input_valid),
        .pcm_dout       (dsp_output_data),
        .pcm_dout_valid (dsp_output_valid),

        .irq            ()
    );

    // Volume Control
    volume_control #(
        .CHANNEL_NUM    (2)
    ) u_volume_control (
        .clk            (pclk),
        .rst_n          (prst_n),
        .enable         (volume_enable),

        .pcm_din        (volume_data_in),
        .pcm_din_valid  (volume_valid_in),
        .pcm_dout       (volume_data_out),
        .pcm_dout_valid (volume_valid_out)
    );

    // Sample Rate Converter
    sample_rate_converter u_src (
        .clk            (pclk),
        .rst_n          (prst_n),
        .enable         (src_enable),

        .pcm_din        (src_data_in),
        .pcm_din_valid  (src_valid_in),
        .pcm_dout       (src_data_out),
        .pcm_dout_valid (src_valid_out)
    );

    // Data Path Muxing
    always_comb begin
        dsp_input_data = 0;
        dsp_input_valid = 0;

        if (i2s_enable && i2s_din_valid) begin
            dsp_input_data = i2s_din_data;
            dsp_input_valid = 1'b1;
        end else if (tdm_enable && tdm_din_valid) begin
            dsp_input_data = tdm_din_data;
            dsp_input_valid = 1'b1;
        end else if (pdm_enable && pdm_dout_valid) begin
            dsp_input_data = pdm_dout_data;
            dsp_input_valid = 1'b1;
        end else if (spdif_enable && spdif_din_valid) begin
            dsp_input_data = spdif_din_data;
            dsp_input_valid = 1'b1;
        end
    end

    // TX Data Path
    assign tx_axis_tdata  = dsp_output_valid ? dsp_output_data : volume_data_out;
    assign tx_axis_tvalid = dsp_output_valid | volume_valid_out;
    assign tx_axis_tkeep  = 8'hFF;
    assign tx_axis_tlast  = 1'b1;

    // RX Data Path
    assign rx_axis_tready = 1'b1;

    // PRDATA muxing
    assign prdata = reg_prdata;
    assign pready = reg_pready;

endmodule
