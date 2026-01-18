// Copyright (c) 2026 YaoGuang SoC Project
// All rights reserved

// Volume Control Module
// Revision: 1.0
// Date: 2026-01-18

`timescale 1ns/1ps

module volume_control #(
    parameter CHANNEL_NUM = 2
) (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         enable,

    // PCM Data Interface
    input  wire [31:0]  pcm_din,
    input  wire         pcm_din_valid,
    output wire [31:0]  pcm_dout,
    output wire         pcm_dout_valid
);

    // Parameters
    localparam DATA_WIDTH = 32;

    // Control Register
    reg  [15:0]  ctrl_reg;

    // Internal Signals
    reg  [7:0]   master_volume;
    reg  [7:0]   ch0_volume;
    reg  [7:0]   ch1_volume;
    reg          mute;
    reg          soft_clip_enable;
    reg          ramp_enable;
    reg  [15:0]  ramp_time;

    // Volume ramp
    reg  [7:0]   current_volume;
    reg  [15:0]  ramp_cnt;
    reg          ramping;

    // Volume gain calculation
    wire [31:0]  ch0_gain;
    wire [31:0]  ch1_gain;

    // Clip detection
    wire         ch0_clip;
    wire         ch1_clip;

    // Input samples
    wire [31:0]  ch0_in;
    wire [31:0]  ch1_in;

    // Output samples
    reg  [31:0]  ch0_out;
    reg  [31:0]  ch1_out;
    reg  [31:0]  pcm_dout_reg;
    reg          pcm_dout_valid_reg;

    // De-interleave input
    assign ch0_in = pcm_din;
    assign ch1_in = pcm_din;

    // Volume ramp
    always @(posedge clk) begin
        if (!rst_n) begin
            current_volume <= 8'd200; // 0dB default
            ramp_cnt       <= 16'd0;
            ramping        <= 1'b0;
        end else if (!enable) begin
            current_volume <= 8'd200;
        end else begin
            if (ramp_enable && !ramping && (master_volume != current_volume)) begin
                ramping <= 1'b1;
                ramp_cnt <= 16'd0;
            end

            if (ramping) begin
                if (ramp_cnt == ramp_time) begin
                    ramping <= 1'b0;
                    current_volume <= master_volume;
                end else begin
                    ramp_cnt <= ramp_cnt + 1'b1;
                    if (master_volume > current_volume) begin
                        current_volume <= current_volume + 1'b1;
                    end else begin
                        current_volume <= current_volume - 1'b1;
                    end
                end
            end
        end
    end

    // Gain calculation (0.5dB steps, range -100dB to +12dB)
    function [31:0] calculate_gain;
        input [7:0] volume_db;
        reg   [31:0] linear_gain;
        integer     i;
        begin
            linear_gain = 32'd1 << 30; // Unity gain at 200 (0dB)
            if (volume_db < 200) begin
                // Attenuation: -0.5dB per step
                for (i = 0; i < (200 - volume_db); i = i + 1) begin
                    linear_gain = (linear_gain * 944) >> 10; // 10^(-0.5/20)
                end
            end else begin
                // Boost: +0.5dB per step
                for (i = 0; i < (volume_db - 200); i = i + 1) begin
                    linear_gain = (linear_gain * 1063) >> 10; // 10^(+0.5/20)
                end
            end
            calculate_gain = linear_gain;
        end
    endfunction

    assign ch0_gain = calculate_gain(ch0_volume);
    assign ch1_gain = calculate_gain(ch1_volume);

    // Volume processing
    wire [63:0] ch0_scaled;
    wire [63:0] ch1_scaled;

    assign ch0_scaled = $signed(ch0_in) * $signed(ch0_gain);
    assign ch1_scaled = $signed(ch1_in) * $signed(ch1_gain);

    // Soft clipping
    function [31:0] soft_clip;
        input [31:0]  data_in;
        reg   [31:0]  abs_data;
        reg   [31:0]  clip_data;
        begin
            abs_data = data_in[31] ? -data_in : data_in;
            if (abs_data > 32'h3F000000) begin
                clip_data = 32'h3F000000;
            end else if (abs_data > 32'h3E800000) begin
                clip_data = abs_data - ((abs_data - 32'h3E800000) >> 2);
            end else begin
                clip_data = abs_data;
            end
            soft_clip = data_in[31] ? -clip_data : clip_data;
        end
    endfunction

    // Clip detection
    assign ch0_clip = (ch0_scaled[62:31] > 32'h7FFFFFFF) || (ch0_scaled[62:31] < -32'h80000000);
    assign ch1_clip = (ch1_scaled[62:31] > 32'h7FFFFFFF) || (ch1_scaled[62:31] < -32'h80000000);

    // Output processing
    always @(posedge clk) begin
        if (!rst_n) begin
            ch0_out <= 32'd0;
            ch1_out <= 32'd0;
        end else if (!enable) begin
            ch0_out <= 32'd0;
            ch1_out <= 32'd0;
        end else begin
            if (mute) begin
                ch0_out <= 32'd0;
                ch1_out <= 32'd0;
            end else begin
                ch0_out <= soft_clip_enable ? soft_clip(ch0_scaled[62:31]) : ch0_scaled[62:31];
                ch1_out <= soft_clip_enable ? soft_clip(ch1_scaled[62:31]) : ch1_scaled[62:31];
            end
        end
    end

    // Interleave output (L/R interleaved format)
    always @(posedge clk) begin
        if (!enable) begin
            pcm_dout_reg <= 32'd0;
            pcm_dout_valid_reg <= 1'b0;
        end else begin
            pcm_dout_reg <= ch0_out; // Output left channel
            pcm_dout_valid_reg <= pcm_din_valid;
        end
    end

    assign pcm_dout       = pcm_dout_reg;
    assign pcm_dout_valid = pcm_dout_valid_reg;

    // Control Register
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ctrl_reg <= 16'd0;
        end else begin
            if (pwrite && psel && penable) begin
                if (paddr == 8'h30) begin
                    ctrl_reg <= pwdata[15:0];
                end
            end
        end
    end

    // Decode control fields
    always @(posedge clk) begin
        master_volume  <= ctrl_reg[7:0];
        ch0_volume     <= ctrl_reg[7:0];
        ch1_volume     <= ctrl_reg[7:0];
        mute           <= ctrl_reg[8];
        soft_clip_enable <= ctrl_reg[9];
        ramp_enable    <= ctrl_reg[10];
        ramp_time      <= ctrl_reg[15:11] * 16'd10; // Convert to cycles
    end

endmodule
