// ============================================================
// Project: YaoGuang ISP Top Level
// Module:  isp_top.sv
// Description: ISP Pipeline Top Integration
// ============================================================

`timescale 1ns/1ps

module isp_top #(
    parameter int NUM_LANES      = 16,
    parameter int MAX_WIDTH      = 3840,
    parameter int MAX_HEIGHT     = 2160,
    parameter int DATA_WIDTH     = 16,
    parameter int HDR_FRAMES     = 2
) (
    // Clock & Reset
    input  logic                    clk_i,
    input  logic                    rst_n_i,
    input  logic                    clk_pixel_i,
    input  logic                    rst_pixel_n_i,

    // MIPI CSI-2 Input
    input  logic [NUM_LANES-1:0]    csi_d_p_i,
    input  logic [NUM_LANES-1:0]    csi_d_n_i,
    input  logic                    csi_clk_p_i,
    input  logic                    csi_clk_n_i,

    // Configuration
    input  logic [31:0]             cfg_reg_addr_i,
    input  logic [31:0]             cfg_reg_wdata_i,
    input  logic                    cfg_reg_write_i,
    input  logic                    cfg_reg_read_i,
    output logic [31:0]             cfg_reg_rdata_o,
    output logic                    cfg_reg_ack_o,

    // Output Interface
    output logic [DATA_WIDTH-1:0]   out_data_o,
    output logic                    out_valid_o,
    input  logic                    out_ready_i,
    output logic [23:0]             out_pixel_x_o,
    output logic [23:0]             out_pixel_y_o,
    output logic                    out_frame_start_o,
    output logic                    out_frame_end_o,

    // Statistics Output
    output logic [15:0]             ae_stats_o,
    output logic [15:0]             awb_r_stats_o,
    output logic [15:0]             awb_g_stats_o,
    output logic [15:0]             awb_b_stats_o,
    output logic [255:0]            hist_stats_o,

    // Status
    output logic                    init_done_o,
    output logic                    overflow_o,
    output logic                    csi_lock_o
);

    // Internal Signals
    logic [DATA_WIDTH-1:0]          raw_data;
    logic                           raw_valid;
    logic                           raw_sop;
    logic                           raw_eop;
    logic [15:0]                    raw_vc;
    logic [7:0]                     raw_dt;

    logic [DATA_WIDTH-1:0]          blc_data;
    logic                           blc_valid;

    logic [DATA_WIDTH-1:0]          dpc_data;
    logic                           dpc_valid;

    logic [DATA_WIDTH-1:0]          lsc_data;
    logic                           lsc_valid;

    logic [23:0]                    wb_data;
    logic                           wb_valid;

    logic [23:0]                    demosaic_data;
    logic                           demosaic_valid;

    logic [23:0]                    ccm_data;
    logic                           ccm_valid;

    logic [23:0]                    gamma_data;
    logic                           gamma_valid;

    logic [23:0]                    nr_data;
    logic                           nr_valid;

    logic [23:0]                    sharp_data;
    logic                           sharp_valid;

    logic [23:0]                    hdr_data;
    logic                           hdr_valid;

    // Pipeline Valid Signals
    logic                           pipeline_valid;
    logic [3:0]                     pipeline_stage;

    // Configuration Registers
    logic [7:0]                     blc_enable;
    logic [7:0]                     blc_offset;
    logic [7:0]                     dpc_enable;
    logic [15:0]                    dpc_threshold;
    logic [7:0]                     lsc_enable;
    logic [11:0]                    lsc_gain_red[17][17];
    logic [11:0]                    lsc_gain_green[17][17];
    logic [11:0]                    lsc_gain_blue[17][17];
    logic [7:0]                     wb_enable;
    logic [11:0]                    wb_gain_r;
    logic [11:0]                    wb_gain_g;
    logic [11:0]                    wb_gain_b;
    logic [7:0]                     demosaic_enable;
    logic [7:0]                     ccm_enable;
    logic [11:0]                    ccm_matrix[9];
    logic [7:0]                     gamma_enable;
    logic [11:0]                    gamma_lut[256];
    logic [7:0]                     nr_enable;
    logic [7:0]                     nr_strength;
    logic [7:0]                     sharp_enable;
    logic [7:0]                     sharp_strength;
    logic [7:0]                     hdr_enable;
    logic [3:0]                     hdr_frames;
    logic [7:0]                     out_format;

    // Status Signals
    logic                           csi_rx_error;
    logic                           pipeline_error;
    logic [1:0]                     overflow_count;

    // ============================================================
    // MIPI CSI-2 Receiver
    // ============================================================
    csi_2_rx #(
        .NUM_LANES(NUM_LANES),
        .DATA_WIDTH(DATA_WIDTH)
    ) u_csi_2_rx (
        .clk_i              (clk_i),
        .rst_n_i            (rst_n_i),
        .csi_d_p_i          (csi_d_p_i),
        .csi_d_n_i          (csi_d_n_i),
        .csi_clk_p_i        (csi_clk_p_i),
        .csi_clk_n_i        (csi_clk_n_i),
        .raw_data_o         (raw_data),
        .raw_valid_o        (raw_valid),
        .raw_sop_o          (raw_sop),
        .raw_eop_o          (raw_eop),
        .raw_vc_o           (raw_vc),
        .raw_dt_o           (raw_dt),
        .lock_o             (csi_lock_o),
        .error_o            (csi_rx_error)
    );

    // ============================================================
    // Black Level Correction
    // ============================================================
    bayer_processing #(
        .DATA_WIDTH(DATA_WIDTH)
    ) u_bayer_processing (
        .clk_i              (clk_pixel_i),
        .rst_n_i            (rst_pixel_n_i),
        .cfg_enable_i       (blc_enable[0]),
        .cfg_offset_i       (blc_offset),
        .cfg_dpc_enable_i   (dpc_enable[0]),
        .cfg_dpc_threshold_i(dpc_threshold),
        .cfg_lsc_enable_i   (lsc_enable[0]),
        .cfg_lsc_gain_red_i (lsc_gain_red),
        .cfg_lsc_gain_green_i(lsc_gain_green),
        .cfg_lsc_gain_blue_i(lsc_gain_blue),
        .cfg_wb_enable_i    (wb_enable[0]),
        .cfg_wb_gain_r_i    (wb_gain_r),
        .cfg_wb_gain_g_i    (wb_gain_g),
        .cfg_wb_gain_b_i    (wb_gain_b),
        .raw_data_i         (raw_data),
        .raw_valid_i        (raw_valid),
        .raw_sop_i          (raw_sop),
        .raw_eop_i          (raw_eop),
        .blc_data_o         (blc_data),
        .blc_valid_o        (blc_valid),
        .dpc_data_o         (dpc_data),
        .dpc_valid_o        (dpc_valid),
        .lsc_data_o         (lsc_data),
        .lsc_valid_o        (lsc_valid),
        .wb_data_o          (wb_data),
        .wb_valid_o         (wb_valid)
    );

    // ============================================================
    // Demosaic
    // ============================================================
    demosaic_unit #(
        .DATA_WIDTH(DATA_WIDTH)
    ) u_demosaic (
        .clk_i              (clk_pixel_i),
        .rst_n_i            (rst_pixel_n_i),
        .cfg_enable_i       (demosaic_enable[0]),
        .bayer_data_i       (wb_data),
        .bayer_valid_i      (wb_valid),
        .rgb_data_o         (demosaic_data),
        .rgb_valid_o        (demosaic_valid)
    );

    // ============================================================
    // Color Correction Matrix
    // ============================================================
    ccm矫正 #(
        .DATA_WIDTH(12)
    ) u_ccm (
        .clk_i              (clk_pixel_i),
        .rst_n_i            (rst_pixel_n_i),
        .cfg_enable_i       (ccm_enable[0]),
        .cfg_matrix_i       (ccm_matrix),
        .rgb_data_i         (demosaic_data),
        .rgb_valid_i        (demosaic_valid),
        .rgb_corrected_o    (ccm_data),
        .rgb_valid_o        (ccm_valid)
    );

    // ============================================================
    // Gamma Correction
    // ============================================================
    gamma_correction #(
        .LUT_SIZE(256)
    ) u_gamma (
        .clk_i              (clk_pixel_i),
        .rst_n_i            (rst_pixel_n_i),
        .cfg_enable_i       (gamma_enable[0]),
        .cfg_lut_i          (gamma_lut),
        .rgb_data_i         (ccm_data),
        .rgb_valid_i        (ccm_valid),
        .rgb_gamma_o        (gamma_data),
        .rgb_valid_o        (gamma_valid)
    );

    // ============================================================
    // Noise Reduction
    // ============================================================
    noise_reduction #(
        .DATA_WIDTH(12)
    ) u_noise_reduction (
        .clk_i              (clk_pixel_i),
        .rst_n_i            (rst_pixel_n_i),
        .cfg_enable_i       (nr_enable[0]),
        .cfg_strength_i     (nr_strength),
        .rgb_data_i         (gamma_data),
        .rgb_valid_i        (gamma_valid),
        .rgb_denoised_o     (nr_data),
        .rgb_valid_o        (nr_valid)
    );

    // ============================================================
    // Edge Enhancement (Sharpening)
    // ============================================================
    edge_enhancement #(
        .DATA_WIDTH(12)
    ) u_edge_enhancement (
        .clk_i              (clk_pixel_i),
        .rst_n_i            (rst_pixel_n_i),
        .cfg_enable_i       (sharp_enable[0]),
        .cfg_strength_i     (sharp_strength),
        .rgb_data_i         (nr_data),
        .rgb_valid_i        (nr_valid),
        .rgb_sharpened_o    (sharp_data),
        .rgb_valid_o        (sharp_valid)
    );

    // ============================================================
    // HDR Fusion (Optional)
    // ============================================================
    generate
        if (HDR_FRAMES > 1) begin : gen_hdr
            hdr_fusion #(
                .DATA_WIDTH(12),
                .HDR_FRAMES(HDR_FRAMES)
            ) u_hdr_fusion (
                .clk_i              (clk_pixel_i),
                .rst_n_i            (rst_pixel_n_i),
                .cfg_enable_i       (hdr_enable[0]),
                .cfg_frames_i       (hdr_frames),
                .rgb_data_i         (sharp_data),
                .rgb_valid_i        (sharp_valid),
                .hdr_fused_o        (hdr_data),
                .hdr_valid_o        (hdr_valid)
            );
        end else begin : gen_no_hdr
            assign hdr_data = sharp_data;
            assign hdr_valid = sharp_valid;
        end
    endgenerate

    // ============================================================
    // Output Formatter
    // ============================================================
    output_formatter #(
        .DATA_WIDTH(12),
        .MAX_WIDTH(MAX_WIDTH),
        .MAX_HEIGHT(MAX_HEIGHT)
    ) u_output_formatter (
        .clk_i              (clk_pixel_i),
        .rst_n_i            (rst_pixel_n_i),
        .cfg_format_i       (out_format),
        .rgb_data_i         (hdr_data),
        .rgb_valid_i        (hdr_valid),
        .out_data_o         (out_data_o),
        .out_valid_o        (out_valid_o),
        .out_ready_i        (out_ready_i),
        .out_pixel_x_o      (out_pixel_x_o),
        .out_pixel_y_o      (out_pixel_y_o),
        .out_frame_start_o  (out_frame_start_o),
        .out_frame_end_o    (out_frame_end_o)
    );

    // ============================================================
    // Statistics Generation
    // ============================================================
    isp_stats u_isp_stats (
        .clk_i              (clk_pixel_i),
        .rst_n_i            (rst_pixel_n_i),
        .rgb_data_i         (ccm_data),
        .rgb_valid_i        (ccm_valid),
        .ae_stats_o         (ae_stats_o),
        .awb_r_stats_o      (awb_r_stats_o),
        .awb_g_stats_o      (awb_g_stats_o),
        .awb_b_stats_o      (awb_b_stats_o),
        .hist_stats_o       (hist_stats_o)
    );

    // ============================================================
    // Configuration Register Block
    // ============================================================
    isp_reg_block u_reg_block (
        .clk_i              (clk_i),
        .rst_n_i            (rst_n_i),
        .cfg_addr_i         (cfg_reg_addr_i),
        .cfg_wdata_i        (cfg_reg_wdata_i),
        .cfg_write_i        (cfg_reg_write_i),
        .cfg_read_i         (cfg_reg_read_i),
        .cfg_rdata_o        (cfg_reg_rdata_o),
        .cfg_ack_o          (cfg_reg_ack_o),
        .blc_enable_o       (blc_enable),
        .blc_offset_o       (blc_offset),
        .dpc_enable_o       (dpc_enable),
        .dpc_threshold_o    (dpc_threshold),
        .lsc_enable_o       (lsc_enable),
        .lsc_gain_red_o     (lsc_gain_red),
        .lsc_gain_green_o   (lsc_gain_green),
        .lsc_gain_blue_o    (lsc_gain_blue),
        .wb_enable_o        (wb_enable),
        .wb_gain_r_o        (wb_gain_r),
        .wb_gain_g_o        (wb_gain_g),
        .wb_gain_b_o        (wb_gain_b),
        .demosaic_enable_o  (demosaic_enable),
        .ccm_enable_o       (ccm_enable),
        .ccm_matrix_o       (ccm_matrix),
        .gamma_enable_o     (gamma_enable),
        .gamma_lut_o        (gamma_lut),
        .nr_enable_o        (nr_enable),
        .nr_strength_o      (nr_strength),
        .sharp_enable_o     (sharp_enable),
        .sharp_strength_o   (sharp_strength),
        .hdr_enable_o       (hdr_enable),
        .hdr_frames_o       (hdr_frames),
        .out_format_o       (out_format),
        .init_done_o        (init_done_o),
        .overflow_o         (pipeline_error)
    );

    // ============================================================
    // Overflow Detection
    // ============================================================
    always_ff @(posedge clk_pixel_i or negedge rst_pixel_n_i) begin
        if (!rst_pixel_n_i) begin
            overflow_count <= '0;
        end else begin
            if (pipeline_error) begin
                overflow_count <= overflow_count + 1;
            end else if (&overflow_count) begin
                overflow_count <= '0;
            end
        end
    end

    assign overflow_o = &overflow_count;

endmodule
