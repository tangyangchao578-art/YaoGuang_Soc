// Copyright (c) 2026 YaoGuang SoC Project
// All rights reserved

// PDM Controller Module
// Revision: 1.0
// Date: 2026-01-18

`timescale 1ns/1ps

module pdm_controller #(
    parameter CHANNEL_NUM = 2
) (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         enable,

    // External PDM Interface
    input  wire         pdm_clk,
    input  wire [CHANNEL_NUM-1:0] pdm_din,
    output wire         lrsel,

    // PCM Data Interface
    output wire [31:0]  pcm_dout,
    output wire         pcm_dout_valid
);

    // Parameters
    localparam OSR_64   = 6'd0;
    localparam OSR_128  = 6'd1;
    localparam OSR_256  = 6'd2;

    localparam DEC_IMP_COEFF = 64;

    // Control Register
    reg  [15:0]  ctrl_reg;

    // Internal Signals
    reg  [2:0]   osr;
    reg  [15:0]  hpf_cutoff;
    reg  [1:0]   channel_select;
    reg          hpf_enable;
    reg          dec_filter_enable;

    // PDM clock domain signals
    reg  [CHANNEL_NUM-1:0] pdm_din_sync;
    reg  [7:0]   pdm_clk_div;
    reg          pdm_clk_en;
    reg  [5:0]   pdm_sample_cnt;
    reg  [CHANNEL_NUM-1:0][63:0] pdm_shift_reg;
    reg  [CHANNEL_NUM-1:0] pdm_valid;
    reg  [31:0]  pdm_data_out [CHANNEL_NUM-1:0];

    // PCM output
    reg  [31:0]  pcm_data_reg;
    reg          pcm_valid_reg;

    // CIC Decimation Filter
    reg  [CHANNEL_NUM-1:0][23:0] cic_s1 [7:0];
    reg  [CHANNEL_NUM-1:0][23:0] cic_s2 [7:0];
    reg  [CHANNEL_NUM-1:0][26:0] cic_s3;
    reg  [CHANNEL_NUM-1:0][31:0] cic_out;

    // LFSR for dithering
    reg  [15:0]  lfsr;

    // Synchronize PDM input
    always @(posedge pdm_clk) begin
        pdm_din_sync <= pdm_din;
    end

    // LFSR for dither
    always @(posedge clk) begin
        lfsr <= {lfsr[14:0], ^lfsr[15:0]};
    end

    // PDM sample counter
    always @(posedge pdm_clk) begin
        if (!enable) begin
            pdm_sample_cnt <= 6'd0;
        end else begin
            if (pdm_sample_cnt == OSR_64 ? 6'd63 : (OSR_128 ? 6'd127 : 6'd255)) begin
                pdm_sample_cnt <= 6'd0;
            end else begin
                pdm_sample_cnt <= pdm_sample_cnt + 1'b1;
            end
        end
    end

    // LRSEL generation (stereo mode)
    assign lrsel = pdm_sample_cnt[5];

    // PDM Shift Registers
    genvar ch;
    generate
        for (ch = 0; ch < CHANNEL_NUM; ch = ch + 1) begin: PDM_CH
            always @(posedge pdm_clk) begin
                if (!enable) begin
                    pdm_shift_reg[ch] <= 64'd0;
                end else begin
                    pdm_shift_reg[ch] <= {pdm_shift_reg[ch][62:0], pdm_din_sync[ch]};
                end
            end

            // Basic PDM to PCM conversion (accumulate and decimate)
            always @(posedge pdm_clk) begin
                if (!enable) begin
                    pdm_data_out[ch] <= 32'd0;
                    pdm_valid[ch]    <= 1'b0;
                end else begin
                    if (pdm_sample_cnt == 6'd0) begin
                        pdm_data_out[ch] <= $signed(pdm_shift_reg[ch]);
                        pdm_valid[ch]    <= 1'b1;
                    end else begin
                        pdm_valid[ch]    <= 1'b0;
                    end
                end
            end
        end
    endgenerate

    // CIC Decimation Filter
    generate
        for (ch = 0; ch < CHANNEL_NUM; ch = ch + 1) begin: CIC_FILTER
            // Stage 1: Comb section (integrators)
            integer i;
            always @(posedge clk) begin
                if (!enable || !dec_filter_enable) begin
                    for (i = 0; i < 8; i = i + 1) begin
                        cic_s1[ch][i] <= 24'd0;
                    end
                end else if (pdm_valid[ch]) begin
                    cic_s1[ch][0] <= $signed(pdm_data_out[ch][23:0]);
                    for (i = 1; i < 8; i = i + 1) begin
                        cic_s1[ch][i] <= cic_s1[ch][i] + cic_s1[ch][i-1];
                    end
                end
            end

            // Stage 2: Integrator section
            always @(posedge clk) begin
                if (!enable || !dec_filter_enable) begin
                    cic_s2[ch][0] <= 24'd0;
                    cic_s2[ch][1] <= 24'd0;
                    cic_s2[ch][2] <= 24'd0;
                    cic_s2[ch][3] <= 24'd0;
                    cic_s2[ch][4] <= 24'd0;
                    cic_s2[ch][5] <= 24'd0;
                    cic_s2[ch][6] <= 24'd0;
                    cic_s2[ch][7] <= 24'd0;
                end else if (pdm_valid[ch]) begin
                    cic_s2[ch][0] <= cic_s1[ch][7];
                    cic_s2[ch][1] <= cic_s2[ch][0] + cic_s2[ch][1];
                    cic_s2[ch][2] <= cic_s2[ch][1] + cic_s2[ch][2];
                    cic_s2[ch][3] <= cic_s2[ch][2] + cic_s2[ch][3];
                    cic_s2[ch][4] <= cic_s2[ch][3] + cic_s2[ch][4];
                    cic_s2[ch][5] <= cic_s2[ch][4] + cic_s2[ch][5];
                    cic_s2[ch][6] <= cic_s2[ch][5] + cic_s2[ch][6];
                    cic_s2[ch][7] <= cic_s2[ch][6] + cic_s2[ch][7];
                end
            end

            // Stage 3: Downsampling and final integrator
            always @(posedge clk) begin
                if (!enable || !dec_filter_enable) begin
                    cic_s3[ch] <= 27'd0;
                end else if (pdm_valid[ch]) begin
                    cic_s3[ch] <= cic_s2[ch][7] + cic_s3[ch];
                    cic_out[ch] <= {{8{cic_s3[ch][26]}}, cic_s3[ch]};
                end
            end
        end
    endgenerate

    // High Pass Filter (remove DC offset)
    reg  [31:0]  hpf_in [CHANNEL_NUM-1:0];
    reg  [31:0]  hpf_out [CHANNEL_NUM-1:0];
    reg  [31:0]  hpf_y_prev [CHANNEL_NUM-1:0];
    reg  [31:0]  hpf_x_prev [CHANNEL_NUM-1:0];
    reg  [15:0]  hpf_alpha;

    always @(posedge clk) begin
        hpf_alpha <= 16'h7FFF - hpf_cutoff;
    end

    generate
        for (ch = 0; ch < CHANNEL_NUM; ch = ch + 1) begin: HPF
            always @(posedge clk) begin
                if (!enable || !hpf_enable) begin
                    hpf_out[ch] <= cic_out[ch];
                end else begin
                    hpf_out[ch] <= cic_out[ch] - cic_out[ch] +
                                   (hpf_x_prev[ch] >> 1) -
                                   (hpf_y_prev[ch] >> 1);
                    hpf_x_prev[ch] <= cic_out[ch];
                    hpf_y_prev[ch] <= hpf_out[ch];
                end
            end
        end
    endgenerate

    // Output Mux
    always @(posedge clk) begin
        if (!enable) begin
            pcm_data_reg <= 32'd0;
            pcm_valid_reg <= 1'b0;
        end else begin
            case (channel_select)
                2'b00:   pcm_data_reg <= hpf_out[0];
                2'b01:   pcm_data_reg <= hpf_out[1];
                default: pcm_data_reg <= hpf_out[0];
            endcase
            pcm_valid_reg <= pdm_valid[0] | pdm_valid[1];
        end
    end

    assign pcm_dout       = pcm_data_reg;
    assign pcm_dout_valid = pcm_valid_reg;

    // Control Register
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ctrl_reg <= 16'd0;
        end else begin
            if (pwrite && psel && penable) begin
                if (paddr == 8'h20) begin
                    ctrl_reg <= pwdata[15:0];
                end
            end
        end
    end

    // Decode control fields
    always @(posedge clk) begin
        osr              <= ctrl_reg[2:0];
        hpf_cutoff       <= ctrl_reg[15:8];
        channel_select   <= ctrl_reg[5:4];
        hpf_enable       <= ctrl_reg[6];
        dec_filter_enable = ctrl_reg[7];
    end

endmodule
