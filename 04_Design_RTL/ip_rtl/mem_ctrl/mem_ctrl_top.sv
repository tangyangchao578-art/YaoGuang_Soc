//-----------------------------------------------------------------------------
// LPDDR5 Memory Controller Top Module
// YaoGuang SoC Project
//-----------------------------------------------------------------------------
// Description:
//   Top-level module for LPDDR5 Memory Controller
//   Integrates AXI slave interface, command queue, scheduler, PHY interface,
//   and ECC encoder/decoder
//-----------------------------------------------------------------------------
// Version: 1.0
// Date: 2026-01-18
//-----------------------------------------------------------------------------

`timescale 1ps/1fs

module mem_ctrl_top #(
    parameter CHANNELS             = 2,
    parameter DATA_WIDTH_PER_CH    = 16,
    parameter AXI_ADDR_WIDTH       = 40,
    parameter AXI_DATA_WIDTH       = 256,
    parameter AXI_ID_WIDTH         = 8,
    parameter CMD_QUEUE_DEPTH      = 64,
    parameter REORDER_DEPTH        = 32,
    parameter ECC_ENABLE           = 1,               // P0: ECC 必选
    parameter TCQ                  = 100
) (
    // ----------------------
    // Clock and Reset
    // ----------------------
    input  wire                             clk_i,
    input  wire                             rst_n_i,

    // ----------------------
    // System Control
    // ----------------------
    input  wire                             init_done_i,      // DRAM initialization complete
    input  wire                             refresh_req_i,    // Refresh request from timer
    output wire                             refresh_ack_o,    // Refresh acknowledge
    output wire                             init_done_o,      // Initialization status

    // ----------------------
    // AXI4 Slave Interface
    // ----------------------
    input  wire [AXI_ID_WIDTH-1:0]          s_axiqos_i,       // QoS ID
    input  wire [3:0]                       s_axiqos_arlen_i, // Burst length
    input  wire [2:0]                       s_axiqos_arsize_i,// Burst size
    input  wire [1:0]                       s_axiqos_arburst_i,// Burst type
    input  wire [AXI_ADDR_WIDTH-1:0]        s_axiqos_araddr_i,// Read address
    input  wire                             s_axiqos_arvalid_i,// Read address valid
    output wire                             s_axiqos_arready_o,// Read address ready
    input  wire [AXI_ID_WIDTH-1:0]          s_axiqos_awid_i,  // Write ID
    input  wire [3:0]                       s_axiqos_awlen_i, // Burst length
    input  wire [2:0]                       s_axiqos_awsize_i,// Burst size
    input  wire [1:0]                       s_axiqos_awburst_i,// Burst type
    input  wire [AXI_ADDR_WIDTH-1:0]        s_axiqos_awaddr_i,// Write address
    input  wire                             s_axiqos_awvalid_i,// Write address valid
    output wire                             s_axiqos_awready_o,// Write address ready
    input  wire [AXI_DATA_WIDTH-1:0]        s_axiqos_wdata_i, // Write data
    input  wire [(AXI_DATA_WIDTH/8)-1:0]    s_axiqos_wstrb_i, // Write strobe
    input  wire                             s_axiqos_wlast_i, // Write last
    input  wire                             s_axiqos_wvalid_i,// Write valid
    output wire                             s_axiqos_wready_o,// Write ready
    output wire [AXI_ID_WIDTH-1:0]          s_axiqos_rid_o,   // Read ID
    output wire [AXI_DATA_WIDTH-1:0]        s_axiqos_rdata_o, // Read data
    output wire [1:0]                       s_axiqos_rresp_o, // Read response
    output wire                             s_axiqos_rlast_o, // Read last
    output wire                             s_axiqos_rvalid_o,// Read valid
    input  wire                             s_axiqos_rready_i,// Read ready
    output wire [AXI_ID_WIDTH-1:0]          s_axiqos_bid_o,   // Write response ID
    output wire [1:0]                       s_axiqos_bresp_o, // Write response
    output wire                             s_axiqos_bvalid_o,// Write response valid
    input  wire                             s_axiqos_bready_i,// Write response ready

    // ----------------------
    // PHY Interface (DFI 4.0)
    // ----------------------
    output wire [(CHANNELS*DATA_WIDTH_PER_CH)-1:0] dfi_dq_o,
    input  wire [(CHANNELS*DATA_WIDTH_PER_CH)-1:0]  dfi_dq_i,
    output wire [CHANNELS-1:0]              dfi_dqs_t_o,
    output wire [(CHANNELS*DATA_WIDTH_PER_CH)-1:0] dfi_dqs_o,
    input  wire [(CHANNELS*DATA_WIDTH_PER_CH)-1:0]  dfi_dqs_i,
    output wire [(CHANNELS*DATA_WIDTH_PER_CH/8)-1:0] dfi_dm_o,
    output wire [(CHANNELS*DATA_WIDTH_PER_CH)-1:0] dfi_dbi_o,
    input  wire [(CHANNELS*DATA_WIDTH_PER_CH/8)-1:0]  dfi_dbi_i,
    output wire [CHANNELS*17-1:0]           dfi_cmd_o,
    input  wire [CHANNELS*5-1:0]            dfi_status_i,
    output wire [CHANNELS-1:0]              dfi_cs_o,
    output wire [CHANNELS*2-1:0]            dfi_ck_o,
    output wire [CHANNELS-1:0]              dfi_cke_o,
    output wire [CHANNELS-1:0]              dfi_odt_o,
    output wire                             dfi_training_o,

    // ----------------------
    // ECC Interface
    // ----------------------
    output wire                             ecc_error_o,      // ECC error detected
    output wire                             ecc_corrected_o,  // Single-bit error corrected
    output wire [7:0]                       ecc_err_cnt_o,    // Error counter
    input  wire                             ecc_test_mode_i,  // ECC test mode
    input  wire                             ecc_err_inj_i,    // Error injection trigger
    input  wire                             ecc_err_type_i,   // 0: single, 1: double

    // ----------------------
    // CSR Interface
    // ----------------------
    input  wire [31:0]                      csr_addr_i,
    input  wire                             csr_write_i,
    input  wire [31:0]                      csr_wdata_i,
    output wire [31:0]                      csr_rdata_o,
    input  wire                             csr_valid_i,
    output wire                             csr_ready_o,

    // ----------------------
    // Status and Debug
    // ----------------------
    output wire [7:0]                       status_o,
    output wire [31:0]                      debug_o
);

    // ----------------------
    // Parameters
    // ----------------------
    localparam DATA_WIDTH = CHANNELS * DATA_WIDTH_PER_CH;  // Total data width
    localparam ECC_DATA_WIDTH = 64;                        // ECC data chunk width
    localparam ECC_PARITY_WIDTH = 8;                       // ECC parity width

    // ----------------------
    // Signals
    // ----------------------
    // Command queue interface
    wire                                    cmd_queue_wr_en;
    wire [AXI_ID_WIDTH+AXI_ADDR_WIDTH+10-1:0] cmd_queue_wr_data;
    wire                                    cmd_queue_full;
    wire                                    cmd_queue_rd_en;
    wire [AXI_ID_WIDTH+AXI_ADDR_WIDTH+10-1:0] cmd_queue_rd_data;
    wire                                    cmd_queue_empty;

    // Read/Write paths
    wire                                    rw_read;
    wire                                    rw_write;
    wire [AXI_ID_WIDTH-1:0]                 rw_id;
    wire [AXI_ADDR_WIDTH-1:0]               rw_addr;
    wire [7:0]                              rw_len;
    wire [2:0]                              rw_size;
    wire [1:0]                              rw_burst;
    wire                                    rw_valid;
    wire                                    rw_ready;

    // Read data path
    wire [DATA_WIDTH-1:0]                   read_data_raw;
    wire [DATA_WIDTH-1:0]                   read_data_ecc;
    wire                                    read_valid;
    wire                                    read_ready;

    // Write data path
    wire [DATA_WIDTH-1:0]                   write_data_raw;
    wire [DATA_WIDTH-1:0]                   write_data_ecc;
    wire                                    write_valid;
    wire                                    write_ready;

    // ECC signals
    wire                                    ecc_err;
    wire                                    ecc_ce;
    wire [7:0]                              ecc_cnt;

    // Scheduler signals
    wire                                    sched_cmd_valid;
    wire                                    sched_cmd_ready;
    wire [15:0]                             sched_cmd_addr;
    wire [3:0]                              sched_cmd_len;
    wire                                    sched_cmd_read;
    wire                                    sched_cmd_write;
    wire [7:0]                              sched_cmd_id;
    wire [2:0]                              sched_cmd_prio;

    // PHY command interface
    wire                                    phy_cmd_valid;
    wire                                    phy_cmd_ready;
    wire [16:0]                             phy_cmd_cs;
    wire [1:0]                              phy_cmd_cke;
    wire [1:0]                              phy_cmd_odt;
    wire [2:0]                              phy_cmd_act;
    wire [1:0]                              phy_cmd_ba;
    wire [6:0]                              phy_cmd_bg;
    wire [7:0]                              phy_cmd_addr;
    wire                                    phy_cmd_we;
    wire                                    phy_cmd_cas;
    wire                                    phy_cmd_ras;

    // ----------------------
    // Module Instantiations
    // ----------------------

    // AXI4 Slave Interface
    mem_ctrl_AXI_slave #(
        .ADDR_WIDTH     (AXI_ADDR_WIDTH),
        .DATA_WIDTH     (AXI_DATA_WIDTH),
        .ID_WIDTH       (AXI_ID_WIDTH),
        .CMD_QUEUE_DEPTH(CMD_QUEUE_DEPTH)
    ) u_AXI_slave (
        .clk_i              (clk_i),
        .rst_n_i            (rst_n_i),
        .s_axiqos_arlen_i   (s_axiqos_arlen_i),
        .s_axiqos_arsize_i  (s_axiqos_arsize_i),
        .s_axiqos_arburst_i (s_axiqos_arburst_i),
        .s_axiqos_araddr_i  (s_axiqos_araddr_i),
        .s_axiqos_arvalid_i (s_axiqos_arvalid_i),
        .s_axiqos_arready_o (s_axiqos_arready_o),
        .s_axiqos_awid_i    (s_axiqos_awid_i),
        .s_axiqos_awlen_i   (s_axiqos_awlen_i),
        .s_axiqos_awsize_i  (s_axiqos_awsize_i),
        .s_axiqos_awburst_i (s_axiqos_awburst_i),
        .s_axiqos_awaddr_i  (s_axiqos_awaddr_i),
        .s_axiqos_awvalid_i (s_axiqos_awvalid_i),
        .s_axiqos_awready_o (s_axiqos_awready_o),
        .s_axiqos_wdata_i   (s_axiqos_wdata_i),
        .s_axiqos_wstrb_i   (s_axiqos_wstrb_i),
        .s_axiqos_wlast_i   (s_axiqos_wlast_i),
        .s_axiqos_wvalid_i  (s_axiqos_wvalid_i),
        .s_axiqos_wready_o  (s_axiqos_wready_o),
        .s_axiqos_rid_o     (s_axiqos_rid_o),
        .s_axiqos_rdata_o   (s_axiqos_rdata_o),
        .s_axiqos_rresp_o   (s_axiqos_rresp_o),
        .s_axiqos_rlast_o   (s_axiqos_rlast_o),
        .s_axiqos_rvalid_o  (s_axiqos_rvalid_o),
        .s_axiqos_rready_i  (s_axiqos_rready_i),
        .s_axiqos_bid_o     (s_axiqos_bid_o),
        .s_axiqos_bresp_o   (s_axiqos_bresp_o),
        .s_axiqos_bvalid_o  (s_axiqos_bvalid_o),
        .s_axiqos_bready_i  (s_axiqos_bready_i),
        .cmd_queue_wr_en_o  (cmd_queue_wr_en),
        .cmd_queue_wr_data_o(cmd_queue_wr_data),
        .cmd_queue_full_i   (cmd_queue_full),
        .read_data_i        (read_data_ecc),
        .read_valid_i       (read_valid),
        .read_ready_o       (read_ready),
        .write_data_o       (write_data_raw),
        .write_valid_o      (write_valid),
        .write_ready_i      (write_ready),
        .status_o           (status_o)
    );

    // Command Queue
    mem_ctrl_cmd_queue #(
        .WIDTH       (AXI_ID_WIDTH + AXI_ADDR_WIDTH + 10),
        .DEPTH       (CMD_QUEUE_DEPTH)
    ) u_cmd_queue (
        .clk_i          (clk_i),
        .rst_n_i        (rst_n_i),
        .wr_en_i        (cmd_queue_wr_en),
        .wr_data_i      (cmd_queue_wr_data),
        .full_o         (cmd_queue_full),
        .rd_en_i        (cmd_queue_rd_en),
        .rd_data_o      (cmd_queue_rd_data),
        .empty_o        (cmd_queue_empty)
    );

    // Command Scheduler
    mem_ctrl_scheduler #(
        .ADDR_WIDTH     (AXI_ADDR_WIDTH),
        .ID_WIDTH       (AXI_ID_WIDTH),
        .CHANNELS       (CHANNELS),
        .REORDER_DEPTH  (REORDER_DEPTH)
    ) u_scheduler (
        .clk_i              (clk_i),
        .rst_n_i            (rst_n_i),
        .cmd_queue_empty_i  (cmd_queue_empty),
        .cmd_queue_rd_data_i(cmd_queue_rd_data),
        .cmd_queue_rd_en_o  (cmd_queue_rd_en),
        .refresh_req_i      (refresh_req_i),
        .refresh_ack_o      (refresh_ack_o),
        .init_done_i        (init_done_i),
        .ecc_error_i        (ecc_err),
        .sched_cmd_valid_o  (sched_cmd_valid),
        .sched_cmd_ready_i  (sched_cmd_ready),
        .sched_cmd_addr_o   (sched_cmd_addr),
        .sched_cmd_len_o    (sched_cmd_len),
        .sched_cmd_read_o   (sched_cmd_read),
        .sched_cmd_write_o  (sched_cmd_write),
        .sched_cmd_id_o     (sched_cmd_id),
        .sched_cmd_prio_o   (sched_cmd_prio)
    );

    // PHY Interface
    mem_ctrl_phy_if #(
        .CHANNELS      (CHANNELS),
        .DATA_WIDTH    (DATA_WIDTH_PER_CH)
    ) u_phy_if (
        .clk_i              (clk_i),
        .rst_n_i            (rst_n_i),
        .sched_cmd_valid_i  (sched_cmd_valid),
        .sched_cmd_ready_o  (sched_cmd_ready),
        .sched_cmd_addr_i   (sched_cmd_addr),
        .sched_cmd_len_i    (sched_cmd_len),
        .sched_cmd_read_i   (sched_cmd_read),
        .sched_cmd_write_i  (sched_cmd_write),
        .sched_cmd_id_i     (sched_cmd_id),
        .write_data_i       (write_data_ecc),
        .write_valid_i      (write_valid),
        .write_ready_o      (write_ready),
        .read_data_o        (read_data_raw),
        .read_valid_o       (read_valid),
        .read_ready_i       (read_ready),
        .dfi_dq_o           (dfi_dq_o),
        .dfi_dq_i           (dfi_dq_i),
        .dfi_dqs_t_o        (dfi_dqs_t_o),
        .dfi_dqs_o          (dfi_dqs_o),
        .dfi_dqs_i          (dfi_dqs_i),
        .dfi_dm_o           (dfi_dm_o),
        .dfi_dbi_o          (dfi_dbi_o),
        .dfi_dbi_i          (dfi_dbi_i),
        .dfi_cmd_o          (dfi_cmd_o),
        .dfi_status_i       (dfi_status_i),
        .dfi_cs_o           (dfi_cs_o),
        .dfi_ck_o           (dfi_ck_o),
        .dfi_cke_o          (dfi_cke_o),
        .dfi_odt_o          (dfi_odt_o),
        .dfi_training_o     (dfi_training_o),
        .csr_addr_i         (csr_addr_i),
        .csr_write_i        (csr_write_i),
        .csr_wdata_i        (csr_wdata_i),
        .csr_rdata_o        (csr_rdata_o),
        .csr_valid_i        (csr_valid_i),
        .csr_ready_o        (csr_ready_o)
    );

    // ECC Encoder/Decoder
    generate
        if (ECC_ENABLE) begin : gen_ecc
            mem_ctrl_ecc #(
                .DATA_WIDTH (DATA_WIDTH)
            ) u_ecc (
                .clk_i            (clk_i),
                .rst_n_i          (rst_n_i),
                .write_data_i     (write_data_raw),
                .write_data_o     (write_data_ecc),
                .read_data_i      (read_data_raw),
                .read_data_o      (read_data_ecc),
                .test_mode_i      (ecc_test_mode_i),
                .err_inj_i        (ecc_err_inj_i),
                .err_type_i       (ecc_err_type_i),
                .error_o          (ecc_err),
                .corrected_o      (ecc_ce),
                .err_cnt_o        (ecc_cnt),
                .csr_addr_i       (csr_addr_i),
                .csr_write_i      (csr_write_i),
                .csr_wdata_i      (csr_wdata_i),
                .csr_rdata_o      (csr_rdata_o),
                .csr_valid_i      (csr_valid_i),
                .csr_ready_o      (csr_ready_o)
            );
        end else begin : gen_no_ecc
            assign write_data_ecc = write_data_raw;
            assign read_data_ecc = read_data_raw;
            assign ecc_err = 1'b0;
            assign ecc_ce = 1'b0;
            assign ecc_cnt = 8'b0;
        end
    endgenerate

    // Outputs
    assign ecc_error_o = ecc_err;
    assign ecc_corrected_o = ecc_ce;
    assign ecc_err_cnt_o = ecc_cnt;
    assign init_done_o = init_done_i;
    assign debug_o = {24'b0, status_o};

endmodule
