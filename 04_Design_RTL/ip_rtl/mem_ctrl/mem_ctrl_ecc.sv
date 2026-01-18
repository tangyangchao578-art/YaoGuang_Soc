//-----------------------------------------------------------------------------
// LPDDR5 Memory Controller SECDED ECC Encoder/Decoder (ASIL-D)
// YaoGuang SoC Project
//-----------------------------------------------------------------------------
// Description:
//   SECDED (Single Error Correction, Double Error Detection) ECC
//   Mandatory for automotive ASIL-D safety compliance
//   Implements 64-bit data + 8-bit parity code (Hamming + parity)
//-----------------------------------------------------------------------------
// Version: 1.0
// Date: 2026-01-18
//-----------------------------------------------------------------------------

`timescale 1ps/1fs

module mem_ctrl_ecc #(
    parameter DATA_WIDTH   = 256,  // Total data width
    parameter TCQ          = 100
) (
    // ----------------------
    // Clock and Reset
    // ----------------------
    input  wire                     clk_i,
    input  wire                     rst_n_i,

    // ----------------------
    // Write Path (Encoder)
    // ----------------------
    input  wire [DATA_WIDTH-1:0]    write_data_i,
    output wire [DATA_WIDTH+DATA_WIDTH/8-1:0] write_data_o,

    // ----------------------
    // Read Path (Decoder)
    // ----------------------
    input  wire [DATA_WIDTH+DATA_WIDTH/8-1:0] read_data_i,
    output wire [DATA_WIDTH-1:0]    read_data_o,

    // ----------------------
    // Test Mode
    // ----------------------
    input  wire                     test_mode_i,
    input  wire                     err_inj_i,
    input  wire                     err_type_i,     // 0: single bit, 1: double bit

    // ----------------------
    // Error Status
    // ----------------------
    output wire                     error_o,        // Any error detected
    output wire                     corrected_o,    // Single-bit error corrected
    output wire [7:0]               err_cnt_o,      // Error counter

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
    localparam CHUNK_WIDTH = 64;      // ECC works on 64-bit chunks
    localparam PARITY_WIDTH = 8;      // 8-bit parity for 64-bit data
    localparam NUM_CHUNKS = DATA_WIDTH / CHUNK_WIDTH;

    // Parity bit positions (Hamming code + overall parity)
    // H7 H6 H5 H4 H3 H2 H1 P (P is overall parity)
    localparam P_POS = 7;
    localparam H1_POS = 0;
    localparam H2_POS = 1;
    localparam H4_POS = 2;
    localparam H8_POS = 3;
    localparam H16_POS = 4;
    localparam H32_POS = 5;
    localparam H64_POS = 6;

    // ----------------------
    // Signals
    // ----------------------
    // Per-chunk signals
    reg  [CHUNK_WIDTH-1:0]          chunk_data_r [0:NUM_CHUNKS-1];
    reg  [PARITY_WIDTH-1:0]         chunk_parity_r [0:NUM_CHUNKS-1];
    reg  [CHUNK_WIDTH-1:0]          chunk_corrected_r [0:NUM_CHUNKS-1];
    reg                             chunk_error_r [0:NUM_CHUNKS-1];
    reg                             chunk_corrected_flag_r [0:NUM_CHUNKS-1];

    // Overall error status
    reg                             any_error_r;
    reg                             any_corrected_r;
    reg  [7:0]                      err_cnt_r;
    reg  [7:0]                      err_cnt_inj_r;

    // Test mode
    reg  [CHUNK_WIDTH-1:0]          test_data_r;
    reg  [CHUNK_WIDTH-1:0]          corrupted_data_r;
    reg                             test_mode_active_r;

    // CSR
    wire                           csr_sel_w;
    wire [31:0]                    csr_rdata_w;

    // ----------------------
    // Assigns
    // ----------------------
    assign error_o = any_error_r;
    assign corrected_o = any_corrected_r;
    assign err_cnt_o = err_cnt_r + err_cnt_inj_r;

    assign csr_sel_w = csr_valid_i && (csr_addr_i[11:0] >= 12'h100 && csr_addr_i[11:0] < 12'h200);
    assign csr_ready_o = csr_valid_i;

    // ----------------------
    // CSR Registers
    // ----------------------
    reg  [31:0]                     csr_ctrl_r;
    reg  [31:0]                     csr_status_r;
    reg  [31:0]                     csr_err_inj_addr_r;
    reg  [31:0]                     csr_err_inj_data_r;

    wire ECC_ENABLE = csr_ctrl_r[0];
    wire TEST_MODE_EN = csr_ctrl_r[1];

    assign csr_rdata_w = csr_sel_w ? (
        (csr_addr_i[9:0] == 10'h100) ? csr_ctrl_r :
        (csr_addr_i[9:0] == 10'h104) ? csr_status_r :
        (csr_addr_i[9:0] == 10'h108) ? {24'b0, err_cnt_r} :
        (csr_addr_i[9:0] == 10'h10C) ? csr_err_inj_addr_r :
        (csr_addr_i[9:0] == 10'h110) ? csr_err_inj_data_r : '0
    ) : '0;
    assign csr_rdata_o = csr_rdata_w;

    always @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            csr_ctrl_r <= 32'b1;  // ECC enabled by default
            csr_status_r <= '0;
            csr_err_inj_addr_r <= '0;
            csr_err_inj_data_r <= '0;
            err_cnt_r <= '0;
            err_cnt_inj_r <= '0;
            test_mode_active_r <= 1'b0;
        end else if (csr_sel_w && csr_write_i) begin
            case (csr_addr_i[9:0])
                10'h100: csr_ctrl_r <= csr_wdata_i;
                10'h108: err_cnt_r <= csr_wdata_i[7:0];  // Clear counter
                10'h10C: csr_err_inj_addr_r <= csr_wdata_i;
                10'h110: csr_err_inj_data_r <= csr_wdata_i;
            endcase
        end else begin
            csr_status_r <= {30'b0, any_error_r, any_corrected_r};
        end
    end

    // ----------------------
    // ECC Encoder (Write Path)
    // ----------------------
    genvar g_i;
    integer j;

    generate
        for (g_i = 0; g_i < NUM_CHUNKS; g_i = g_i + 1) begin : gen_encoder
            wire [CHUNK_WIDTH-1:0] data_in;
            wire [PARITY_WIDTH-1:0] parity_out;
            wire [CHUNK_WIDTH-1:0] data_out;
            wire [PARITY_WIDTH-1:0] parity_out_corrupted;

            assign data_in = write_data_i[g_i*CHUNK_WIDTH +: CHUNK_WIDTH];
            assign write_data_o[g_i*(CHUNK_WIDTH+PARITY_WIDTH) +: CHUNK_WIDTH] = data_out;
            assign write_data_o[g_i*(CHUNK_WIDTH+PARITY_WIDTH) + CHUNK_WIDTH +: PARITY_WIDTH] = parity_out_corrupted;

            // ECC encoder for this chunk
            ecc_encoder #(
                .DATA_WIDTH (CHUNK_WIDTH)
            ) u_encoder (
                .data_i     (data_in),
                .parity_o   (parity_out)
            );

            // Error injection in test mode
            assign data_out = test_mode_i ? corrupted_data_r : data_in;
            assign parity_out_corrupted = test_mode_i ? {parity_out[6:0], ~parity_out[7]} : parity_out;
        end
    endgenerate

    // ----------------------
    // ECC Decoder (Read Path)
    // ----------------------
    generate
        for (g_i = 0; g_i < NUM_CHUNKS; g_i = g_i + 1) begin : gen_decoder
            wire [CHUNK_WIDTH-1:0] data_in;
            wire [PARITY_WIDTH-1:0] parity_in;
            wire [CHUNK_WIDTH-1:0] data_out;
            wire [CHUNK_WIDTH-1:0] data_corrected;
            wire [PARITY_WIDTH-1:0] parity_calc;
            wire [7:0] syndrome;
            wire error_detected;
            wire error_corrected;

            assign data_in = read_data_i[g_i*(CHUNK_WIDTH+PARITY_WIDTH) +: CHUNK_WIDTH];
            assign parity_in = read_data_i[g_i*(CHUNK_WIDTH+PARITY_WIDTH) + CHUNK_WIDTH +: PARITY_WIDTH];

            // Recalculate parity
            ecc_encoder #(
                .DATA_WIDTH (CHUNK_WIDTH)
            ) u_parity_calc (
                .data_i     (data_in),
                .parity_o   (parity_calc)
            );

            // Syndrome calculation
            assign syndrome = parity_in ^ parity_calc;

            // Error detection and correction
            ecc_corrector #(
                .DATA_WIDTH (CHUNK_WIDTH)
            ) u_corrector (
                .data_i         (data_in),
                .syndrome_i     (syndrome),
                .data_o         (data_corrected),
                .error_o        (error_detected),
                .corrected_o    (error_corrected)
            );

            // Register outputs
            always @(posedge clk_i or negedge rst_n_i) begin
                if (!rst_n_i) begin
                    chunk_corrected_r[g_i] <= '0;
                    chunk_error_r[g_i] <= 1'b0;
                    chunk_corrected_flag_r[g_i] <= 1'b0;
                end else begin
                    chunk_corrected_r[g_i] <= data_corrected;
                    chunk_error_r[g_i] <= error_detected & !error_corrected;  // Double-bit error
                    chunk_corrected_flag_r[g_i] <= error_corrected;  // Single-bit error corrected
                end
            end
        end
    endgenerate

    // ----------------------
    // Error Aggregation
    // ----------------------
    always @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            any_error_r <= 1'b0;
            any_corrected_r <= 1'b0;
        end else begin
            any_error_r <= 1'b0;
            any_corrected_r <= 1'b0;

            for (j = 0; j < NUM_CHUNKS; j = j + 1) begin
                any_error_r <= any_error_r | chunk_error_r[j];
                any_corrected_r <= any_corrected_r | chunk_corrected_flag_r[j];
            end

            // Count errors
            if (any_error_r | any_corrected_r) begin
                err_cnt_r <= err_cnt_r + 1'b1;
            end
        end
    end

    // ----------------------
    // Test Mode - Error Injection
    // ----------------------
    always @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            test_data_r <= '0;
            corrupted_data_r <= '0;
        end else begin
            if (err_inj_i) begin
                test_data_r <= write_data_i[63:0];  // Inject in first chunk

                if (err_type_i) begin
                    // Double-bit error
                    corrupted_data_r[csr_err_inj_addr_r[5:0]] <= ~write_data_i[csr_err_inj_addr_r[5:0]];
                    corrupted_data_r[csr_err_inj_data_r[5:0]] <= ~write_data_i[csr_err_inj_data_r[5:0]];
                end else begin
                    // Single-bit error
                    corrupted_data_r[csr_err_inj_addr_r[5:0]] <= ~write_data_i[csr_err_inj_addr_r[5:0]];
                end
            end else begin
                corrupted_data_r <= write_data_i[63:0];
            end
        end
    end

    // ----------------------
    // Output Assignment
    // ----------------------
    integer k;
    always @(*) begin
        for (k = 0; k < NUM_CHUNKS; k = k + 1) begin
            read_data_o[k*CHUNK_WIDTH +: CHUNK_WIDTH] = chunk_corrected_r[k];
        end
    end

endmodule

//-----------------------------------------------------------------------------
// ECC Encoder Module
// Generates 8-bit SECDED parity for 64-bit data
//-----------------------------------------------------------------------------
module ecc_encoder #(
    parameter DATA_WIDTH = 64
) (
    input  wire [DATA_WIDTH-1:0]    data_i,
    output wire [7:0]               parity_o
);

    // Hamming code parity bits + overall parity
    // P0 covers all even bits (1,3,5,...)
    // P1 covers bits 0,1,3,4,6,7,... (positions where bit 1 of index is set)
    // P2 covers bits 0,1,2,3,8,9,10,11,... (positions where bit 2 of index is set)
    // etc.

    wire p0, p1, p2, p3, p4, p5, p6, p7;

    // P0: Overall parity (even parity)
    assign p0 = ^data_i;

    // P1: Position 1 (bit 0 of index)
    assign p1 = ^{
        data_i[0], data_i[2], data_i[4], data_i[6], data_i[8], data_i[10], data_i[12], data_i[14],
        data_i[16], data_i[18], data_i[20], data_i[22], data_i[24], data_i[26], data_i[28], data_i[30],
        data_i[32], data_i[34], data_i[36], data_i[38], data_i[40], data_i[42], data_i[44], data_i[46],
        data_i[48], data_i[50], data_i[52], data_i[54], data_i[56], data_i[58], data_i[60], data_i[62]
    };

    // P2: Position 2 (bit 1 of index)
    assign p2 = ^{
        data_i[0], data_i[1], data_i[4], data_i[5], data_i[8], data_i[9], data_i[12], data_i[13],
        data_i[16], data_i[17], data_i[20], data_i[21], data_i[24], data_i[25], data_i[28], data_i[29],
        data_i[32], data_i[33], data_i[36], data_i[37], data_i[40], data_i[41], data_i[44], data_i[45],
        data_i[48], data_i[49], data_i[52], data_i[53], data_i[56], data_i[57], data_i[60], data_i[61]
    };

    // P4: Position 4 (bit 2 of index)
    assign p3 = ^{
        data_i[0], data_i[1], data_i[2], data_i[3], data_i[8], data_i[9], data_i[10], data_i[11],
        data_i[12], data_i[13], data_i[14], data_i[15], data_i[24], data_i[25], data_i[26], data_i[27],
        data_i[28], data_i[29], data_i[30], data_i[31], data_i[40], data_i[41], data_i[42], data_i[43],
        data_i[44], data_i[45], data_i[46], data_i[47], data_i[56], data_i[57], data_i[58], data_i[59]
    };

    // P8: Position 8 (bit 3 of index)
    assign p4 = ^{
        data_i[0], data_i[1], data_i[2], data_i[3], data_i[4], data_i[5], data_i[6], data_i[7],
        data_i[16], data_i[17], data_i[18], data_i[19], data_i[20], data_i[21], data_i[22], data_i[23],
        data_i[24], data_i[25], data_i[26], data_i[27], data_i[28], data_i[29], data_i[30], data_i[31],
        data_i[48], data_i[49], data_i[50], data_i[51], data_i[52], data_i[53], data_i[54], data_i[55]
    };

    // P16: Position 16 (bit 4 of index)
    assign p5 = ^{
        data_i[0], data_i[1], data_i[2], data_i[3], data_i[4], data_i[5], data_i[6], data_i[7],
        data_i[8], data_i[9], data_i[10], data_i[11], data_i[12], data_i[13], data_i[14], data_i[15],
        data_i[32], data_i[33], data_i[34], data_i[35], data_i[36], data_i[37], data_i[38], data_i[39],
        data_i[40], data_i[41], data_i[42], data_i[43], data_i[44], data_i[45], data_i[46], data_i[47]
    };

    // P32: Position 32 (bit 5 of index)
    assign p6 = ^{
        data_i[32], data_i[33], data_i[34], data_i[35], data_i[36], data_i[37], data_i[38], data_i[39],
        data_i[40], data_i[41], data_i[42], data_i[43], data_i[44], data_i[45], data_i[46], data_i[47],
        data_i[48], data_i[49], data_i[50], data_i[51], data_i[52], data_i[53], data_i[54], data_i[55],
        data_i[56], data_i[57], data_i[58], data_i[59], data_i[60], data_i[61], data_i[62], data_i[63]
    };

    // P64: Position 64 (bit 6 of index) - not used for 64-bit data
    assign p7 = 1'b0;

    // Output: {P7, P6, P4, P2, P1, P0} - re-ordered for standard SECDED
    assign parity_o = {p0, p1, p2, p3, p4, p5, p6, p7};

endmodule

//-----------------------------------------------------------------------------
// ECC Corrector Module
// Detects and corrects errors based on syndrome
//-----------------------------------------------------------------------------
module ecc_corrector #(
    parameter DATA_WIDTH = 64
) (
    input  wire [DATA_WIDTH-1:0]    data_i,
    input  wire [7:0]               syndrome_i,
    output wire [DATA_WIDTH-1:0]    data_o,
    output wire                     error_o,       // Uncorrectable error (2-bit)
    output wire                     corrected_o    // Single-bit error corrected
);

    wire [6:0] syndrome_nonzero;
    wire [5:0] error_pos;

    assign syndrome_nonzero = |syndrome_i[6:0];
    assign error_pos = syndrome_i[6:1];  // Syndrome bits 1-6 indicate error position

    // Error correction: flip the erroneous bit
    assign data_o = syndrome_nonzero ?
                    (data_i ^ (1'b1 << error_pos)) : data_i;

    // Single-bit correction indicator
    assign corrected_o = syndrome_nonzero && (syndrome_i[7] == 1'b0);

    // Double-bit error: syndrome non-zero with overall parity error
    // This indicates an uncorrectable 2-bit error
    assign error_o = syndrome_nonzero && (syndrome_i[7] == 1'b1);

endmodule
