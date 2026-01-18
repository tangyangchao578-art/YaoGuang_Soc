//-----------------------------------------------------------------------------
// LPDDR5 Memory Controller Command Scheduler
// YaoGuang SoC Project
//-----------------------------------------------------------------------------
// Description:
//   DRAM command scheduler with QoS, bank management, and refresh handling
//   Optimizes bank utilization and implements priority-based scheduling
//-----------------------------------------------------------------------------
// Version: 1.0
// Date: 2026-01-18
//-----------------------------------------------------------------------------

`timescale 1ps/1fs

module mem_ctrl_scheduler #(
    parameter ADDR_WIDTH     = 40,
    parameter ID_WIDTH       = 8,
    parameter CHANNELS       = 2,
    parameter REORDER_DEPTH  = 32,
    parameter TCQ            = 100
) (
    // ----------------------
    // Clock and Reset
    // ----------------------
    input  wire                     clk_i,
    input  wire                     rst_n_i,

    // ----------------------
    // Command Queue Interface
    // ----------------------
    input  wire                     cmd_queue_empty_i,
    input  wire [ID_WIDTH+ADDR_WIDTH+10-1:0] cmd_queue_rd_data_i,
    output wire                     cmd_queue_rd_en_o,

    // ----------------------
    // Refresh Interface
    // ----------------------
    input  wire                     refresh_req_i,
    output wire                     refresh_ack_o,

    // ----------------------
    // Initialization
    // ----------------------
    input  wire                     init_done_i,

    // ----------------------
    // Error Handling
    // ----------------------
    input  wire                     ecc_error_i,

    // ----------------------
    // Scheduled Command Output
    // ----------------------
    output wire                     sched_cmd_valid_o,
    input  wire                     sched_cmd_ready_i,
    output wire [15:0]              sched_cmd_addr_o,
    output wire [3:0]               sched_cmd_len_o,
    output wire                     sched_cmd_read_o,
    output wire                     sched_cmd_write_o,
    output wire [ID_WIDTH-1:0]      sched_cmd_id_o,
    output wire [2:0]               sched_cmd_prio_o
);

    // ----------------------
    // Parameters
    // ----------------------
    localparam PRIO_WIDTH   = 3;
    localparam NUM_BANKS    = 16;
    localparam MAX_PRIO     = 7;

    // ----------------------
    // Command decode
    // ----------------------
    wire                    cmd_write;
    wire [3:0]              cmd_len;
    wire [2:0]              cmd_size;
    wire [1:0]              cmd_burst;
    wire [ADDR_WIDTH-1:0]   cmd_addr;
    wire [ID_WIDTH-1:0]     cmd_id;

    assign {cmd_id, cmd_addr, cmd_write, cmd_len, cmd_size, cmd_burst} = cmd_queue_rd_data_i;

    // ----------------------
    // Signals
    // ----------------------
    // Reorder buffer
    reg  [REORDER_DEPTH-1:0][ADDR_WIDTH+ID_WIDTH+5-1:0] rob_r;
    reg  [REORDER_DEPTH-1:0][PRIO_WIDTH-1:0]             rob_prio_r;
    reg  [REORDER_DEPTH-1:0]                             rob_valid_r;
    reg  [REORDER_DEPTH-1:0]                             rob_write_r;
    reg  [5:0]                                           rob_cnt_r;
    reg  [5:0]                                           rob_head_r;
    reg  [5:0]                                           rob_tail_r;

    // Priority queues
    reg  [7:0][REORDER_DEPTH-1:0]                        prio_queue_r;
    reg  [7:0]                                           prio_cnt_r;

    // Bank state
    reg  [NUM_BANKS-1:0]                                 bank_open_r;
    reg  [NUM_BANKS-1:0][15:0]                           bank_row_r;

    // Scheduler
    reg  [2:0]                                           current_prio_r;
    reg  [5:0]                                           sched_cnt_r;
    reg                          sched_valid_r;
    reg  [15:0]                  sched_addr_r;
    reg  [3:0]                   sched_len_r;
    reg                          sched_read_r;
    reg                          sched_write_r;
    reg  [ID_WIDTH-1:0]          sched_id_r;
    reg  [2:0]                   sched_prio_r;

    // Refresh
    reg                          refresh_pending_r;
    reg                          in_refresh_r;

    // ----------------------
    // Assigns
    // ----------------------
    assign cmd_queue_rd_en_o = !cmd_queue_empty_i & !refresh_pending_r &
                               (rob_cnt_r < REORDER_DEPTH);

    assign refresh_ack_o = refresh_pending_r;

    assign sched_cmd_valid_o = sched_valid_r;
    assign sched_cmd_addr_o  = sched_addr_r;
    assign sched_cmd_len_o   = sched_len_r;
    assign sched_cmd_read_o  = sched_read_r;
    assign sched_cmd_write_o = sched_write_r;
    assign sched_cmd_id_o    = sched_id_r;
    assign sched_cmd_prio_o  = sched_prio_r;

    // ----------------------
    // Command Decode
    // ----------------------
    wire [2:0] cmd_prio_w;
    assign cmd_prio_w = MAX_PRIO;  // Default priority, can be modified by QoS

    // ----------------------
    // Reorder Buffer Management
    // ----------------------
    always @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            rob_cnt_r <= '0;
            rob_head_r <= '0;
            rob_tail_r <= '0;
            rob_valid_r <= '0;
            rob_write_r <= '0;
            prio_cnt_r <= '0;
        end else begin
            // Enqueue new command
            if (cmd_queue_rd_en_o && !cmd_queue_empty_i) begin
                rob_r[rob_tail_r] <= {cmd_addr, cmd_id, cmd_len, cmd_write};
                rob_prio_r[rob_tail_r] <= cmd_prio_w;
                rob_valid_r[rob_tail_r] <= 1'b1;
                rob_write_r[rob_tail_r] <= cmd_write;
                rob_tail_r <= (rob_tail_r + 1'b1) % REORDER_DEPTH;
                rob_cnt_r <= rob_cnt_r + 1'b1;
            end

            // Dequeue completed command
            if (sched_cmd_valid_o && sched_cmd_ready_i) begin
                rob_valid_r[rob_head_r] <= 1'b0;
                rob_head_r <= (rob_head_r + 1'b1) % REORDER_DEPTH;
                rob_cnt_r <= rob_cnt_r - 1'b1;
            end

            // Refresh handling - drain buffer
            if (refresh_pending_r && !in_refresh_r) begin
                in_refresh_r <= 1'b1;
            end else if (in_refresh_r) begin
                if (rob_cnt_r == '0) begin
                    in_refresh_r <= 1'b0;
                    refresh_pending_r <= 1'b0;
                end
            end
        end
    end

    // ----------------------
    // Refresh Request
    // ----------------------
    always @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            refresh_pending_r <= 1'b0;
        end else begin
            if (refresh_req_i && !in_refresh_r) begin
                refresh_pending_r <= 1'b1;
            end
        end
    end

    // ----------------------
    // Priority-based Scheduling
    // ----------------------
    integer i, j;
    reg [2:0] selected_prio;
    reg [5:0] selected_idx;
    reg found_cmd;

    always @(*) begin
        selected_prio = MAX_PRIO;
        selected_idx = '0;
        found_cmd = 1'b0;

        if (init_done_i && !refresh_pending_r && rob_cnt_r > 0) begin
            // Priority-based selection
            for (i = 0; i <= MAX_PRIO; i = i + 1) begin
                if (!found_cmd && prio_cnt_r[i] > 0) begin
                    for (j = 0; j < REORDER_DEPTH; j = j + 1) begin
                        if (rob_valid_r[j] && (rob_prio_r[j] == i)) begin
                            selected_prio = i;
                            selected_idx = j;
                            found_cmd = 1'b1;
                            break;
                        end
                    end
                end
            end
        end
    end

    // ----------------------
    // Scheduler Output
    // ----------------------
    always @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            sched_valid_r <= 1'b0;
            sched_addr_r <= '0;
            sched_len_r <= '0;
            sched_read_r <= 1'b0;
            sched_write_r <= 1'b0;
            sched_id_r <= '0;
            sched_prio_r <= '0;
        end else begin
            if (sched_cmd_ready_i) begin
                sched_valid_r <= 1'b0;
            end

            if (found_cmd && !sched_valid_r && init_done_i) begin
                sched_valid_r <= 1'b1;
                sched_addr_r <= rob_r[selected_idx][ADDR_WIDTH+ID_WIDTH+5-1:ID_WIDTH+5];
                sched_id_r <= rob_r[selected_idx][ID_WIDTH+4:5];
                sched_len_r <= rob_r[selected_idx][4:1];
                sched_write_r <= rob_r[selected_idx][0];
                sched_read_r <= !rob_r[selected_idx][0];
                sched_prio_r <= rob_prio_r[selected_idx];
            end
        end
    end

    // ----------------------
    // Bank Management
    // ----------------------
    wire [3:0] bank_addr_w;
    wire [15:0] row_addr_w;

    assign bank_addr_w = sched_addr_r[5:2];  // Bank from address
    assign row_addr_w = sched_addr_r[21:6];  // Row from address

    always @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            bank_open_r <= '0;
            bank_row_r <= '0;
        end else begin
            if (sched_cmd_valid_o && sched_cmd_ready_i) begin
                // Open row for write
                if (sched_cmd_write_o && !bank_open_r[bank_addr_w]) begin
                    bank_open_r[bank_addr_w] <= 1'b1;
                    bank_row_r[bank_addr_w] <= row_addr_w;
                end
                // Open row for read
                if (sched_cmd_read_o && !bank_open_r[bank_addr_w]) begin
                    bank_open_r[bank_addr_w] <= 1'b1;
                    bank_row_r[bank_addr_w] <= row_addr_w;
                end
                // Precharge on different row
                if ((sched_cmd_write_o || sched_cmd_read_o) &&
                    bank_open_r[bank_addr_w] &&
                    (bank_row_r[bank_addr_w] != row_addr_w)) begin
                    bank_open_r[bank_addr_w] <= 1'b0;
                end
            end
        end
    end

endmodule
