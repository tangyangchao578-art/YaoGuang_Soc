//-----------------------------------------------------------------------------
// LPDDR5 Memory Controller AXI4 Slave Interface
// YaoGuang SoC Project
//-----------------------------------------------------------------------------
// Description:
//   AXI4 Slave interface for memory controller
//   Handles read/write transactions, manages command queue
//-----------------------------------------------------------------------------
// Version: 1.0
// Date: 2026-01-18
//-----------------------------------------------------------------------------

`timescale 1ps/1fs

module mem_ctrl_AXI_slave #(
    parameter ADDR_WIDTH       = 40,
    parameter DATA_WIDTH       = 256,
    parameter ID_WIDTH         = 8,
    parameter CMD_QUEUE_DEPTH  = 64,
    parameter TCQ              = 100
) (
    // ----------------------
    // Clock and Reset
    // ----------------------
    input  wire                     clk_i,
    input  wire                     rst_n_i,

    // ----------------------
    // AXI4 Address Channel (Read)
    // ----------------------
    input  wire [3:0]               s_axiqos_arlen_i,   // Burst length
    input  wire [2:0]               s_axiqos_arsize_i,  // Burst size
    input  wire [1:0]               s_axiqos_arburst_i, // Burst type
    input  wire [ADDR_WIDTH-1:0]    s_axiqos_araddr_i,  // Read address
    input  wire                     s_axiqos_arvalid_i, // Read address valid
    output wire                     s_axiqos_arready_o, // Read address ready

    // ----------------------
    // AXI4 Address Channel (Write)
    // ----------------------
    input  wire [ID_WIDTH-1:0]      s_axiqos_awid_i,    // Write ID
    input  wire [3:0]               s_axiqos_awlen_i,   // Burst length
    input  wire [2:0]               s_axiqos_awsize_i,  // Burst size
    input  wire [1:0]               s_axiqos_awburst_i, // Burst type
    input  wire [ADDR_WIDTH-1:0]    s_axiqos_awaddr_i,  // Write address
    input  wire                     s_axiqos_awvalid_i, // Write address valid
    output wire                     s_axiqos_awready_o, // Write address ready

    // ----------------------
    // AXI4 Write Data Channel
    // ----------------------
    input  wire [DATA_WIDTH-1:0]    s_axiqos_wdata_i,   // Write data
    input  wire [(DATA_WIDTH/8)-1:0] s_axiqos_wstrb_i,  // Write strobe
    input  wire                     s_axiqos_wlast_i,   // Write last
    input  wire                     s_axiqos_wvalid_i,  // Write valid
    output wire                     s_axiqos_wready_o,  // Write ready

    // ----------------------
    // AXI4 Read Data Channel
    // ----------------------
    output wire [ID_WIDTH-1:0]      s_axiqos_rid_o,     // Read ID
    output wire [DATA_WIDTH-1:0]    s_axiqos_rdata_o,   // Read data
    output wire [1:0]               s_axiqos_rresp_o,   // Read response
    output wire                     s_axiqos_rlast_o,   // Read last
    output wire                     s_axiqos_rvalid_o,  // Read valid
    input  wire                     s_axiqos_rready_i,  // Read ready

    // ----------------------
    // AXI4 Write Response Channel
    // ----------------------
    output wire [ID_WIDTH-1:0]      s_axiqos_bid_o,     // Write response ID
    output wire [1:0]               s_axiqos_bresp_o,   // Write response
    output wire                     s_axiqos_bvalid_o,  // Write response valid
    input  wire                     s_axiqos_bready_i,  // Write response ready

    // ----------------------
    // Command Queue Interface
    // ----------------------
    output wire                     cmd_queue_wr_en_o,
    output wire [ID_WIDTH+ADDR_WIDTH+10-1:0] cmd_queue_wr_data_o,
    input  wire                     cmd_queue_full_i,

    // ----------------------
    // Read Data Path (from ECC)
    // ----------------------
    input  wire [DATA_WIDTH-1:0]    read_data_i,
    input  wire                     read_valid_i,
    output wire                     read_ready_o,

    // ----------------------
    // Write Data Path (to ECC)
    // ----------------------
    output wire [DATA_WIDTH-1:0]    write_data_o,
    output wire                     write_valid_o,
    input  wire                     write_ready_i,

    // ----------------------
    // Status
    // ----------------------
    output wire [7:0]               status_o
);

    // ----------------------
    // Parameters
    // ----------------------
    localparam RESP_OKAY  = 2'b00;
    localparam RESP_EXOKAY = 2'b01;
    localparam RESP_SLVERR = 2'b10;
    localparam RESP_DECERR = 2'b11;

    // ----------------------
    // Signals
    // ----------------------
    // Address channel
    reg                             ar_ready_r;
    reg                             aw_ready_r;
    reg  [ID_WIDTH-1:0]             aw_id_r;
    reg  [ADDR_WIDTH-1:0]           aw_addr_r;
    reg  [3:0]                      aw_len_r;
    reg  [2:0]                      aw_size_r;
    reg  [1:0]                      aw_burst_r;

    // Write data channel
    reg                             w_ready_r;
    reg  [DATA_WIDTH-1:0]           w_data_r;
    reg  [(DATA_WIDTH/8)-1:0]       w_strb_r;
    reg                             w_last_r;

    // Read data channel
    reg                             r_valid_r;
    reg  [ID_WIDTH-1:0]             r_id_r;
    reg  [DATA_WIDTH-1:0]           r_data_r;
    reg                             r_last_r;

    // Write response channel
    reg                             b_valid_r;
    reg  [ID_WIDTH-1:0]             b_id_r;

    // Command packing
    reg  [ID_WIDTH+ADDR_WIDTH+10-1:0] cmd_data_r;
    reg                             cmd_wr_en_r;

    // Write transaction tracking
    reg                             write_in_progress_r;
    reg  [3:0]                      write_beat_cnt_r;
    reg  [ID_WIDTH-1:0]             write_id_r;
    reg  [ADDR_WIDTH-1:0]           write_addr_r;
    reg  [3:0]                      write_len_r;
    reg  [2:0]                      write_size_r;
    reg  [1:0]                      write_burst_r;

    // Read transaction tracking
    reg                             read_in_progress_r;
    reg  [3:0]                      read_beat_cnt_r;
    reg  [ID_WIDTH-1:0]             read_id_r;
    reg  [ADDR_WIDTH-1:0]           read_addr_r;
    reg  [3:0]                      read_len_r;
    reg  [2:0]                      read_size_r;
    reg  [1:0]                      read_burst_r;

    // Status
    wire                            axi_error_w;
    wire                            write_done_w;
    wire                            read_done_w;

    // ----------------------
    // Assigns
    // ----------------------
    assign s_axiqos_arready_o = ar_ready_r;
    assign s_axiqos_awready_o = aw_ready_r;
    assign s_axiqos_wready_o  = w_ready_r;

    assign s_axiqos_rid_o     = r_id_r;
    assign s_axiqos_rdata_o   = r_data_r;
    assign s_axiqos_rresp_o   = axi_error_w ? RESP_SLVERR : RESP_OKAY;
    assign s_axiqos_rlast_o   = r_last_r;
    assign s_axiqos_rvalid_o  = r_valid_r;

    assign s_axiqos_bid_o     = b_id_r;
    assign s_axiqos_bresp_o   = axi_error_w ? RESP_SLVERR : RESP_OKAY;
    assign s_axiqos_bvalid_o  = b_valid_r;

    assign cmd_queue_wr_en_o  = cmd_wr_en_r;
    assign cmd_queue_wr_data_o = cmd_data_r;

    assign write_data_o       = w_data_r;
    assign write_valid_o      = write_in_progress_r & w_ready_r & s_axiqos_wvalid_i;
    assign read_ready_o       = s_axiqos_rready_i & r_valid_r;

    assign status_o           = {6'b0, cmd_queue_full_i, write_in_progress_r};

    // ----------------------
    // Address Channel (Read)
    // ----------------------
    always @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            ar_ready_r <= 1'b0;
            read_in_progress_r <= 1'b0;
        end else begin
            if (s_axiqos_arvalid_i && ar_ready_r) begin
                // Capture read transaction
                read_id_r    <= s_axiqos_awid_i;  // Note: using same ID source
                read_addr_r  <= s_axiqos_araddr_i;
                read_len_r   <= s_axiqos_arlen_i;
                read_size_r  <= s_axiqos_arsize_i;
                read_burst_r <= s_axiqos_arburst_i;
                read_beat_cnt_r <= 4'b0;
                read_in_progress_r <= 1'b1;

                // Pack command
                cmd_data_r <= {s_axiqos_awid_i, s_axiqos_araddr_i, 1'b0, 1'b1,
                              s_axiqos_arlen_i, s_axiqos_arsize_i, s_axiqos_arburst_i};
                cmd_wr_en_r <= 1'b1;
            end else begin
                cmd_wr_en_r <= 1'b0;
                if (read_done_w) begin
                    read_in_progress_r <= 1'b0;
                end
            end

            // AR ready
            ar_ready_r <= !read_in_progress_r & !cmd_queue_full_i;
        end
    end

    // ----------------------
    // Address Channel (Write)
    // ----------------------
    always @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            aw_ready_r <= 1'b0;
            write_in_progress_r <= 1'b0;
        end else begin
            if (s_axiqos_awvalid_i && aw_ready_r) begin
                // Capture write transaction
                write_id_r   <= s_axiqos_awid_i;
                write_addr_r <= s_axiqos_awaddr_i;
                write_len_r  <= s_axiqos_awlen_i;
                write_size_r <= s_axiqos_awsize_i;
                write_burst_r<= s_axiqos_awburst_i;
                write_beat_cnt_r <= 4'b0;
                write_in_progress_r <= 1'b1;

                // Pack command
                cmd_data_r <= {s_axiqos_awid_i, s_axiqos_awaddr_i, 1'b1, 1'b1,
                              s_axiqos_awlen_i, s_axiqos_awsize_i, s_axiqos_awburst_i};
                cmd_wr_en_r <= 1'b1;
            end else begin
                cmd_wr_en_r <= 1'b0;
                if (write_done_w) begin
                    write_in_progress_r <= 1'b0;
                end
            end

            // AW ready
            aw_ready_r <= !write_in_progress_r & !cmd_queue_full_i;
        end
    end

    // ----------------------
    // Write Data Channel
    // ----------------------
    always @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            w_ready_r <= 1'b0;
            w_data_r <= '0;
            w_strb_r <= '0;
            w_last_r <= 1'b0;
        end else begin
            if (s_axiqos_wvalid_i && w_ready_r) begin
                w_data_r <= s_axiqos_wdata_i;
                w_strb_r <= s_axiqos_wstrb_i;
                w_last_r <= s_axiqos_wlast_i;
                write_beat_cnt_r <= write_beat_cnt_r + 1'b1;
            end

            // W ready when write in progress and not stalled
            w_ready_r <= write_in_progress_r & write_ready_i;
        end
    end

    // ----------------------
    // Read Data Channel
    // ----------------------
    always @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            r_valid_r <= 1'b0;
            r_id_r <= '0;
            r_data_r <= '0;
            r_last_r <= 1'b0;
        end else begin
            if (read_valid_i && read_ready_o) begin
                r_data_r <= read_data_i;
                r_last_r <= (read_beat_cnt_r == read_len_r);
                r_id_r <= read_id_r;
                r_valid_r <= 1'b1;
                read_beat_cnt_r <= read_beat_cnt_r + 1'b1;
            end else if (s_axiqos_rready_i && r_valid_r) begin
                r_valid_r <= 1'b0;
            end
        end
    end

    assign read_done_w = r_valid_r & s_axiqos_rready_i & r_last_r;

    // ----------------------
    // Write Response Channel
    // ----------------------
    always @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            b_valid_r <= 1'b0;
            b_id_r <= '0;
        end else begin
            if (write_done_w && !b_valid_r) begin
                b_id_r <= write_id_r;
                b_valid_r <= 1'b1;
            end else if (s_axiqos_bready_i && b_valid_r) begin
                b_valid_r <= 1'b0;
            end
        end
    end

    assign write_done_w = write_in_progress_r & w_last_r & s_axiqos_wvalid_i & w_ready_r;

    // ----------------------
    // Error Detection
    // ----------------------
    assign axi_error_w = 1'b0;  // Placeholder for error detection logic

endmodule
