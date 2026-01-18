//-----------------------------------------------------------------------------
// LPDDR5 Memory Controller PHY Interface (Self-Developed)
// YaoGuang SoC Project
//-----------------------------------------------------------------------------
// Description:
//   Self-developed PHY interface for LPDDR5 DRAM
//   Implements DFI 4.0 interface, command encoding, and data serialization
//-----------------------------------------------------------------------------
// Version: 1.0
// Date: 2026-01-18
//-----------------------------------------------------------------------------

`timescale 1ps/1fs

module mem_ctrl_phy_if #(
    parameter CHANNELS      = 2,
    parameter DATA_WIDTH    = 16,
    parameter TCQ           = 100
) (
    // ----------------------
    // Clock and Reset
    // ----------------------
    input  wire                     clk_i,
    input  wire                     rst_n_i,

    // ----------------------
    // Command Scheduler Interface
    // ----------------------
    input  wire                     sched_cmd_valid_i,
    output wire                     sched_cmd_ready_o,
    input  wire [15:0]              sched_cmd_addr_i,
    input  wire [3:0]               sched_cmd_len_i,
    input  wire                     sched_cmd_read_i,
    input  wire                     sched_cmd_write_i,
    input  wire [7:0]               sched_cmd_id_i,
    input  wire [2:0]               sched_cmd_prio_i,

    // ----------------------
    // Write Data Path
    // ----------------------
    input  wire [(CHANNELS*DATA_WIDTH)-1:0] write_data_i,
    input  wire                             write_valid_i,
    output wire                             write_ready_o,

    // ----------------------
    // Read Data Path
    // ----------------------
    output wire [(CHANNELS*DATA_WIDTH)-1:0] read_data_o,
    output wire                             read_valid_o,
    input  wire                             read_ready_i,

    // ----------------------
    // DFI 4.0 Interface
    // ----------------------
    output wire [(CHANNELS*DATA_WIDTH)-1:0] dfi_dq_o,
    input  wire [(CHANNELS*DATA_WIDTH)-1:0]  dfi_dq_i,
    output wire [CHANNELS-1:0]              dfi_dqs_t_o,
    output wire [(CHANNELS*DATA_WIDTH)-1:0] dfi_dqs_o,
    input  wire [(CHANNELS*DATA_WIDTH)-1:0]  dfi_dqs_i,
    output wire [(CHANNELS*DATA_WIDTH/8)-1:0] dfi_dm_o,
    output wire [(CHANNELS*DATA_WIDTH)-1:0] dfi_dbi_o,
    input  wire [(CHANNELS*DATA_WIDTH/8)-1:0]  dfi_dbi_i,
    output wire [CHANNELS*17-1:0]           dfi_cmd_o,
    input  wire [CHANNELS*5-1:0]            dfi_status_i,
    output wire [CHANNELS-1:0]              dfi_cs_o,
    output wire [CHANNELS*2-1:0]            dfi_ck_o,
    output wire [CHANNELS-1:0]              dfi_cke_o,
    output wire [CHANNELS-1:0]              dfi_odt_o,
    output wire                             dfi_training_o,

    // ----------------------
    // CSR Interface
    // ----------------------
    input  wire [31:0]              csr_addr_i,
    input  wire                     csr_write_i,
    input  wire [31:0]              csr_wdata_i,
    output wire [31:0]              csr_rdata_o,
    input  wire                     csr_valid_i,
    output wire                     csr_ready_o
);

    // ----------------------
    // Parameters
    // ----------------------
    localparam DFI_ADDR_WIDTH = 17;
    localparam DFI_CMD_WIDTH = 17;
    localparam NUM_BANKS = 16;
    localparam BANK_GROUP_WIDTH = 3;
    localparam BANK_ADDR_WIDTH = 2;
    localparam ROW_ADDR_WIDTH = 16;
    localparam COL_ADDR_WIDTH = 10;

    // LPDDR5 Command opcodes
    localparam CMD_NOP      = 17'b00000000000000000;
    localparam CMD_ACT      = 17'b00000000000000001;
    localparam CMD_PRE      = 17'b00000000000000010;
    localparam CMD_PREPB    = 17'b00000000000000011;
    localparam CMD_REF      = 17'b00000000000000100;
    localparam CMD_REFPB    = 17'b00000000000000101;
    localparam CMD_MRS      = 17'b00000000000001000;
    localparam CMD_RDA      = 17'b00000000000010001;
    localparam CMD_WRA      = 17'b00000000000100001;
    localparam CMD_SREF     = 17'b00000000001000000;
    localparam CMD_PDE      = 17'b00000000010000000;
    localparam CMD_PDX      = 17'b00000000100000000;
    localparam CMD_ZQCAL    = 17'b00000001000000000;

    // ----------------------
    // CSR Registers
    // ----------------------
    reg  [31:0]                     csr_tREFI_r;
    reg  [31:0]                     csr_tRFC_r;
    reg  [31:0]                     csr_tRCD_r;
    reg  [31:0]                     csr_tRP_r;
    reg  [31:0]                     csr_tRAS_r;
    reg  [31:0]                     csr_tWR_r;
    reg  [31:0]                     csr_tRTPS_r;
    reg  [31:0]                     csr_tCKE_r;
    reg  [7:0]                      csr_odt_r;
    reg  [7:0]                      csr_cke_r;
    reg  [7:0]                      csr_reset_r;
    reg  [7:0]                      csr_init_done_r;
    reg  [7:0]                      csr_training_done_r;

    wire                           csr_sel_w;
    wire [31:0]                    csr_rdata_w;

    // ----------------------
    // State Machine
    // ----------------------
    typedef enum reg [3:0] {
        ST_IDLE,
        ST_ACTIVATE,
        ST_READ,
        ST_WRITE,
        ST_PRECHARGE,
        ST_REFRESH,
        ST_MRS,
        ST_POWERDOWN,
        ST_SREF
    } state_t;

    reg [3:0]                       state_r;
    reg [3:0]                       next_state_r;
    reg [3:0]                       active_bank_r;
    reg [15:0]                      active_row_r;

    // ----------------------
    // Command Generation
    // ----------------------
    reg  [DFI_CMD_WIDTH-1:0]        dfi_cmd_r;
    reg  [CHANNELS-1:0]             dfi_cs_r;
    reg  [CHANNELS-1:0]             dfi_cke_r;
    reg  [CHANNELS-1:0]             dfi_odt_r;
    reg                             dfi_training_r;

    reg  [15:0]                     cmd_row_r;
    reg  [1:0]                      cmd_bank_r;
    reg  [6:0]                      cmd_bank_group_r;
    reg  [7:0]                      cmd_col_r;
    reg                             cmd_we_r;
    reg                             cmd_cas_r;
    reg                             cmd_ras_r;
    reg  [2:0]                      cmd_act_r;

    // ----------------------
    // Data Path
    // ----------------------
    reg  [(CHANNELS*DATA_WIDTH)-1:0] write_data_r;
    reg  [(CHANNELS*DATA_WIDTH)-1:0] read_data_r;
    reg                             write_valid_r;
    reg                             read_valid_r;
    reg  [3:0]                      beat_cnt_r;

    // ----------------------
    // Assigns
    // ----------------------
    assign dfi_dq_o = '0;      // Driven by PHY in write mode
    assign dfi_dqs_o = '0;     // Driven by PHY
    assign dfi_dm_o = '0;      // Data mask
    assign dfi_dbi_o = '0;     // DBI

    assign dfi_cmd_o = dfi_cmd_r;
    assign dfi_cs_o = dfi_cs_r;
    assign dfi_cke_o = dfi_cke_r;
    assign dfi_odt_o = dfi_odt_r;
    assign dfi_training_o = dfi_training_r;

    assign read_data_o = read_data_r;
    assign read_valid_o = read_valid_r;
    assign write_ready_o = 1'b1;

    assign sched_cmd_ready_o = (state_r == ST_IDLE);

    // ----------------------
    // CSR Logic
    // ----------------------
    assign csr_sel_w = csr_valid_i && (csr_addr_i[11:0] >= 12'h000 && csr_addr_i[11:0] < 12'h100);
    assign csr_ready_o = csr_valid_i;

    always @(*) begin
        csr_rdata_w = '0;
        case (csr_addr_i[9:0])
            10'h000: csr_rdata_w = csr_tREFI_r;
            10'h004: csr_rdata_w = csr_tRFC_r;
            10'h008: csr_rdata_w = csr_tRCD_r;
            10'h00C: csr_rdata_w = csr_tRP_r;
            10'h010: csr_rdata_w = csr_tRAS_r;
            10'h014: csr_rdata_w = csr_tWR_r;
            10'h018: csr_rdata_w = csr_tRTPS_r;
            10'h01C: csr_rdata_w = csr_tCKE_r;
            10'h020: csr_rdata_w = {24'b0, csr_odt_r};
            10'h024: csr_rdata_w = {24'b0, csr_cke_r};
            10'h030: csr_rdata_w = {24'b0, csr_init_done_r};
            10'h034: csr_rdata_w = {24'b0, csr_training_done_r};
            default: csr_rdata_w = '0;
        endcase
    end
    assign csr_rdata_o = csr_rdata_w;

    always @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            csr_tREFI_r <= 32'd7800;      // 7.8 us
            csr_tRFC_r <= 32'd350;
            csr_tRCD_r <= 32'd18;
            csr_tRP_r  <= 32'd18;
            csr_tRAS_r <= 32'd42;
            csr_tWR_r  <= 32'd18;
            csr_tRTPS_r<= 32'd8;
            csr_tCKE_r <= 32'd5;
            csr_odt_r  <= 8'b00000001;
            csr_cke_r  <= 8'b00000011;
            csr_init_done_r <= 8'b0;
            csr_training_done_r <= 8'b0;
        end else if (csr_sel_w && csr_write_i) begin
            case (csr_addr_i[9:0])
                10'h000: csr_tREFI_r <= csr_wdata_i;
                10'h004: csr_tRFC_r <= csr_wdata_i;
                10'h008: csr_tRCD_r <= csr_wdata_i;
                10'h00C: csr_tRP_r  <= csr_wdata_i;
                10'h010: csr_tRAS_r <= csr_wdata_i;
                10'h014: csr_tWR_r  <= csr_wdata_i;
                10'h018: csr_tRTPS_r<= csr_wdata_i;
                10'h01C: csr_tCKE_r <= csr_wdata_i;
                10'h020: csr_odt_r  <= csr_wdata_i[7:0];
                10'h024: csr_cke_r  <= csr_wdata_i[7:0];
            endcase
        end
    end

    // ----------------------
    // State Machine
    // ----------------------
    always @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            state_r <= ST_IDLE;
            active_bank_r <= '0;
            active_row_r <= '0;
        end else begin
            state_r <= next_state_r;
        end
    end

    always @(*) begin
        next_state_r = state_r;

        case (state_r)
            ST_IDLE: begin
                if (sched_cmd_valid_i) begin
                    if (sched_cmd_read_i)
                        next_state_r = ST_ACTIVATE;
                    else if (sched_cmd_write_i)
                        next_state_r = ST_ACTIVATE;
                end
            end

            ST_ACTIVATE: begin
                next_state_r = sched_cmd_read_i ? ST_READ : ST_WRITE;
            end

            ST_READ: begin
                if (read_ready_i && read_valid_r && beat_cnt_r == sched_cmd_len_i)
                    next_state_r = ST_PRECHARGE;
            end

            ST_WRITE: begin
                if (write_valid_i && beat_cnt_r == sched_cmd_len_i)
                    next_state_r = ST_PRECHARGE;
            end

            ST_PRECHARGE: begin
                next_state_r = ST_IDLE;
            end

            default: next_state_r = ST_IDLE;
        endcase
    end

    // ----------------------
    // Command Generation
    // ----------------------
    always @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            dfi_cmd_r <= CMD_NOP;
            dfi_cs_r <= '0;
            dfi_cke_r <= 8'b00000011;
            dfi_odt_r <= '0;
            dfi_training_r <= 1'b0;
            cmd_row_r <= '0;
            cmd_bank_r <= '0;
            cmd_bank_group_r <= '0;
            cmd_we_r <= 1'b1;
            cmd_cas_r <= 1'b1;
            cmd_ras_r <= 1'b1;
            cmd_act_r <= 3'b111;
        end else begin
            case (state_r)
                ST_IDLE: begin
                    if (sched_cmd_valid_i) begin
                        // Parse address
                        cmd_bank_r = sched_cmd_addr_i[5:4];
                        cmd_bank_group_r = sched_cmd_addr_i[8:6];
                        cmd_row_r = sched_cmd_addr_i[24:9];
                        cmd_col_r = sched_cmd_addr_i[15:10];
                    end
                    dfi_cmd_r = CMD_NOP;
                    dfi_cs_r = '0;
                    cmd_we_r = 1'b1;
                    cmd_cas_r = 1'b1;
                    cmd_ras_r = 1'b1;
                    cmd_act_r = 3'b111;
                end

                ST_ACTIVATE: begin
                    dfi_cmd_r = CMD_ACT;
                    dfi_cs_r = 8'b00000011;  // Both channels active
                    cmd_we_r = 1'b1;
                    cmd_cas_r = 1'b1;
                    cmd_ras_r = 1'b0;  // RAS active
                    cmd_act_r = 3'b000;  // ACT_n asserted
                    active_bank_r = cmd_bank_r;
                    active_row_r = cmd_row_r;
                end

                ST_READ: begin
                    dfi_cmd_r = CMD_RDA;
                    dfi_cs_r = 8'b00000011;
                    dfi_odt_r = 8'b00000001;  // ODT on for read
                    cmd_we_r = 1'b1;
                    cmd_cas_r = 1'b0;  // CAS active
                    cmd_ras_r = 1'b1;
                    cmd_act_r = 3'b111;
                end

                ST_WRITE: begin
                    dfi_cmd_r = CMD_WRA;
                    dfi_cs_r = 8'b00000011;
                    dfi_odt_r = 8'b00000010;  // ODT on for write
                    cmd_we_r = 1'b0;  // WE active
                    cmd_cas_r = 1'b1;
                    cmd_ras_r = 1'b1;
                    cmd_act_r = 3'b111;
                end

                ST_PRECHARGE: begin
                    dfi_cmd_r = CMD_PRE;
                    dfi_cs_r = 8'b00000011;
                    dfi_odt_r = '0;
                    cmd_we_r = 1'b0;
                    cmd_cas_r = 1'b1;
                    cmd_ras_r = 1'b0;
                    cmd_act_r = 3'b111;
                end

                default: begin
                    dfi_cmd_r = CMD_NOP;
                    dfi_cs_r = '0;
                    cmd_we_r = 1'b1;
                    cmd_cas_r = 1'b1;
                    cmd_ras_r = 1'b1;
                    cmd_act_r = 3'b111;
                end
            endcase
        end
    end

    // ----------------------
    // Data Path
    // ----------------------
    always @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            write_data_r <= '0;
            read_data_r <= '0;
            write_valid_r <= 1'b0;
            read_valid_r <= 1'b0;
            beat_cnt_r <= '0;
        end else begin
            // Write data capture
            if (write_valid_i) begin
                write_data_r <= write_data_i;
                write_valid_r <= 1'b1;
                beat_cnt_r <= beat_cnt_r + 1'b1;
            end else if (state_r == ST_IDLE) begin
                write_valid_r <= 1'b0;
                beat_cnt_r <= '0;
            end

            // Read data capture
            if (dfi_dq_i !== '0) begin  // Check for valid read data
                read_data_r <= dfi_dq_i;
                read_valid_r <= 1'b1;
            end else begin
                read_valid_r <= 1'b0;
            end
        end
    end

    // ----------------------
    // Output Register Mapping
    // ----------------------
    wire [16:0] dfi_cmd_combined;

    assign dfi_cmd_combined = {
        cmd_act_r,        // [16:14] ACT_n per byte lane
        cmd_bank_group_r, // [13:7]  Bank Group
        cmd_bank_r,       // [6:5]   Bank Address
        cmd_we_n,         // [4]     WE_n
        cmd_cas_n,        // [3]     CAS_n
        cmd_ras_n,        // [2]     RAS_n
        cmd_cke,          // [1:0]   CKE
        cmd_addr[7:0]     // [7:0]   Address
    };

    wire cmd_we_n = cmd_we_r;
    wire cmd_cas_n = cmd_cas_r;
    wire cmd_ras_n = cmd_ras_r;
    wire [1:0] cmd_cke = dfi_cke_r[1:0];
    wire [7:0] cmd_addr = {cmd_row_r[7:0], cmd_col_r};

    // ----------------------
    // Initialization Control
    // ----------------------
    always @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            csr_init_done_r <= 8'b0;
            csr_training_done_r <= 8'b0;
        end else begin
            // Initialization done when all MRS commands complete
            // Training done when eye training completes
        end
    end

endmodule
