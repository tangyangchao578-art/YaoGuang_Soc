// Copyright (c) 2026 YaoGuang SoC Project
// All rights reserved

// Audio Register File Module
// Revision: 1.0
// Date: 2026-01-18

`timescale 1ns/1ps

module audio_regfile (
    // APB Interface
    input  wire         pclk,
    input  wire         prst_n,
    input  wire [11:0]  paddr,
    input  wire         pwrite,
    input  wire [31:0]  pwdata,
    output reg  [31:0]  prdata,
    input  wire         psel,
    input  wire         penable,
    output reg          pready,

    // Version
    input  wire [31:0]  version,

    // Module Enables
    output reg          i2s_enable,
    output reg          tdm_enable,
    output reg          pdm_enable,
    output reg          spdif_enable,
    output reg          dsp_enable,
    output reg          volume_enable,
    output reg          src_enable,
    output reg          eq_enable,
    output reg          drc_enable,

    // Interrupt
    output reg          irq
);

    // Address decoding
    localparam REG_AUDIO_CTRL    = 12'h000;
    localparam REG_AUDIO_STAT    = 12'h004;
    localparam REG_AUDIO_INT_EN  = 12'h008;
    localparam REG_AUDIO_INT_STAT = 12'h00C;
    localparam REG_I2S_CTRL      = 12'h010;
    localparam REG_I2S_STAT      = 12'h014;
    localparam REG_TDM_CTRL      = 12'h018;
    localparam REG_TDM_STAT      = 12'h01C;
    localparam REG_PDM_CTRL      = 12'h020;
    localparam REG_PDM_STAT      = 12'h024;
    localparam REG_SPDIF_CTRL    = 12'h028;
    localparam REG_SPDIF_STAT    = 12'h02C;
    localparam REG_VOL_MASTER    = 12'h030;
    localparam REG_VOL_CH0       = 12'h034;
    localparam REG_VOL_CH1       = 12'h038;
    localparam REG_SRC_CTRL      = 12'h040;
    localparam REG_SRC_RATIO     = 12'h044;
    localparam REG_EQ_CTRL       = 12'h050;
    localparam REG_EQ_BAND0      = 12'h054;
    localparam REG_EQ_BAND1      = 12'h058;
    localparam REG_EQ_BAND2      = 12'h05C;
    localparam REG_DSP_CTRL      = 12'h100;
    localparam REG_DSP_STAT      = 12'h104;

    // Control register
    reg  [31:0]  audio_ctrl;
    reg  [31:0]  audio_stat;
    reg  [31:0]  audio_int_en;
    reg  [31:0]  audio_int_stat;
    reg  [31:0]  i2s_ctrl;
    reg  [31:0]  i2s_stat;
    reg  [31:0]  tdm_ctrl;
    reg  [31:0]  tdm_stat;
    reg  [31:0]  pdm_ctrl;
    reg  [31:0]  pdm_stat;
    reg  [31:0]  spdif_ctrl;
    reg  [31:0]  spdif_stat;
    reg  [31:0]  vol_master;
    reg  [31:0]  vol_ch0;
    reg  [31:0]  vol_ch1;
    reg  [31:0]  src_ctrl;
    reg  [31:0]  src_ratio;
    reg  [31:0]  eq_ctrl;
    reg  [31:0]  eq_band0;
    reg  [31:0]  eq_band1;
    reg  [31:0]  eq_band2;
    reg  [31:0]  dsp_ctrl;
    reg  [31:0]  dsp_stat;

    // Status register bits
    wire i2s_tx_empty;
    wire i2s_rx_full;
    wire tdm_tx_empty;
    wire tdm_rx_full;
    wire pdm_data_valid;
    wire spdif_tx_done;
    wire spdif_rx_done;
    wire dsp_irq;
    wire dsp_busy;

    // Interrupt sources
    wire i2s_int;
    wire tdm_int;
    wire pdm_int;
    wire spdif_int;
    wire dsp_int;

    assign i2s_int = i2s_rx_full;
    assign tdm_int = tdm_rx_full;
    assign pdm_int = pdm_data_valid;
    assign spdif_int = spdif_rx_done;
    assign dsp_int = dsp_irq;

    // APB read
    always @(posedge pclk) begin
        if (!prst_n) begin
            prdata <= 32'd0;
        end else if (psel && penable && !pwrite) begin
            case (paddr)
                REG_AUDIO_CTRL:   prdata <= audio_ctrl;
                REG_AUDIO_STAT:   prdata <= audio_stat;
                REG_AUDIO_INT_EN: prdata <= audio_int_en;
                REG_AUDIO_INT_STAT: prdata <= audio_int_stat;
                REG_I2S_CTRL:     prdata <= i2s_ctrl;
                REG_I2S_STAT:     prdata <= i2s_stat;
                REG_TDM_CTRL:     prdata <= tdm_ctrl;
                REG_TDM_STAT:     prdata <= tdm_stat;
                REG_PDM_CTRL:     prdata <= pdm_ctrl;
                REG_PDM_STAT:     prdata <= pdm_stat;
                REG_SPDIF_CTRL:   prdata <= spdif_ctrl;
                REG_SPDIF_STAT:   prdata <= spdif_stat;
                REG_VOL_MASTER:   prdata <= vol_master;
                REG_VOL_CH0:      prdata <= vol_ch0;
                REG_VOL_CH1:      prdata <= vol_ch1;
                REG_SRC_CTRL:     prdata <= src_ctrl;
                REG_SRC_RATIO:    prdata <= src_ratio;
                REG_EQ_CTRL:      prdata <= eq_ctrl;
                REG_EQ_BAND0:     prdata <= eq_band0;
                REG_EQ_BAND1:     prdata <= eq_band1;
                REG_EQ_BAND2:     prdata <= eq_band2;
                REG_DSP_CTRL:     prdata <= dsp_ctrl;
                REG_DSP_STAT:     prdata <= dsp_stat;     default:          prdata <= 32'd0;
            endcase
        end
    end

    // APB write
    always @(posedge pclk) begin
        if (!prst_n) begin
            audio_ctrl     <= 32'd0;
            audio_int_en   <= 32'd0;
            audio_int_stat <= 32'd0;
            i2s_ctrl       <= 32'd0;
            tdm_ctrl       <= 32'd0;
            pdm_ctrl       <= 32'd0;
            spdif_ctrl     <= 32'd0;
            vol_master     <= 32'd0;
            vol_ch0        <= 32'd0;
            vol_ch1        <= 32'd0;
            src_ctrl       <= 32'd0;
            src_ratio      <= 32'd0;
            eq_ctrl        <= 32'd0;
            eq_band0       <= 32'd0;
            eq_band1       <= 32'd0;
            eq_band2       <= 32'd0;
            dsp_ctrl       <= 32'd0;
        end else if (psel && penable && pwrite) begin
            case (paddr)
                REG_AUDIO_CTRL: begin
                    audio_ctrl <= pwdata;
                end
                REG_AUDIO_INT_EN: begin
                    audio_int_en <= pwdata;
                end
                REG_AUDIO_INT_STAT: begin
                    audio_int_stat <= audio_int_stat & ~pwdata;
                end
                REG_I2S_CTRL: begin
                    i2s_ctrl <= pwdata;
                end
                REG_TDM_CTRL: begin
                    tdm_ctrl <= pwdata;
                end
                REG_PDM_CTRL: begin
                    pdm_ctrl <= pwdata;
                end
                REG_SPDIF_CTRL: begin
                    spdif_ctrl <= pwdata;
                end
                REG_VOL_MASTER: begin
                    vol_master <= pwdata;
                end
                REG_VOL_CH0: begin
                    vol_ch0 <= pwdata;
                end
                REG_VOL_CH1: begin
                    vol_ch1 <= pwdata;
                end
                REG_SRC_CTRL: begin
                    src_ctrl <= pwdata;
                end
                REG_SRC_RATIO: begin
                    src_ratio <= pwdata;
                end
                REG_EQ_CTRL: begin
                    eq_ctrl <= pwdata;
                end
                REG_EQ_BAND0: begin
                    eq_band0 <= pwdata;
                end
                REG_EQ_BAND1: begin
                    eq_band1 <= pwdata;
                end
                REG_EQ_BAND2: begin
                    eq_band2 <= pwdata;
                end
                REG_DSP_CTRL: begin
                    dsp_ctrl <= pwdata;
                end
            endcase
        end
    end

    // Module enables from control registers
    always @(posedge pclk) begin
        i2s_enable    <= i2s_ctrl[0];
        tdm_enable    <= tdm_ctrl[0];
        pdm_enable    <= pdm_ctrl[0];
        spdif_enable  <= spdif_ctrl[0];
        dsp_enable    <= dsp_ctrl[0];
        volume_enable <= 1'b1;
        src_enable    <= src_ctrl[0];
        eq_enable     <= eq_ctrl[0];
        drc_enable    <= eq_ctrl[1];
    end

    // Status register update
    always @(posedge pclk) begin
        audio_stat <= {
            20'd0,
            dsp_busy,
            dsp_irq,
            spdif_rx_done,
            spdif_tx_done,
            pdm_data_valid,
            tdm_rx_full,
            tdm_tx_empty,
            i2s_rx_full,
            i2s_tx_empty
        };

        i2s_stat <= {30'd0, i2s_rx_full, i2s_tx_empty};
        tdm_stat <= {30'd0, tdm_rx_full, tdm_tx_empty};
        pdm_stat <= {31'd0, pdm_data_valid};
        spdif_stat <= {30'd0, spdif_rx_done, spdif_tx_done};
        dsp_stat <= {31'd0, dsp_busy};
    end

    // Interrupt generation
    always @(posedge pclk) begin
        if (!prst_n) begin
            irq <= 1'b0;
        end else begin
            irq <= (i2s_int && audio_int_en[0]) ||
                   (tdm_int && audio_int_en[1]) ||
                   (pdm_int && audio_int_en[2]) ||
                   (spdif_int && audio_int_en[3]) ||
                   (dsp_int && audio_int_en[4]);
        end
    end

    // Ready signal
    always @(posedge pclk) begin
        pready <= psel && penable;
    end

endmodule
