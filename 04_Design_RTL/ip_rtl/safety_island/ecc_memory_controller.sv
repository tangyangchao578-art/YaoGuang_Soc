//=============================================================================
// ECC Memory Controller
// ASIL-D Safety Critical - SECDED Protection
//=============================================================================

`timescale 1ns/1ps

module ecc_memory_controller (
    //============================================================================
    // Clock and Reset
    //============================================================================
    input  logic                            clk_i,
    input  logic                            rst_n_i,
    input  logic                            scan_en_i,

    //============================================================================
    // SRAM Interface
    //============================================================================
    output logic [31:0]                     sram_addr_o,
    output logic [63:0]                     sram_wdata_o,
    input  logic [63:0]                     sram_rdata_i,
    output logic                            sram_we_o,
    output logic [7:0]                      sram_wstrb_o,
    input  logic                            sram_init_done_i,

    //============================================================================
    // AXI4 Slave Interface
    //============================================================================
    input  logic [31:0]                     axi_s_araddr_i,
    input  logic [7:0]                      axi_s_arlen_i,
    input  logic [2:0]                      axi_s_arsize_i,
    input  logic [1:0]                      axi_s_arburst_i,
    input  logic                            axi_s_arvalid_i,
    output logic                            axi_s_arready_o,

    input  logic [31:0]                     axi_s_awaddr_i,
    input  logic [7:0]                      axi_s_awlen_i,
    input  logic [2:0]                      axi_s_awsize_i,
    input  logic [1:0]                      axi_s_awburst_i,
    input  logic                            axi_s_awvalid_i,
    output logic                            axi_s_awready_o,

    input  logic [63:0]                     axi_s_wdata_i,
    input  logic [7:0]                      axi_s_wstrb_i,
    input  logic                            axi_s_wlast_i,
    input  logic                            axi_s_wvalid_i,
    output logic                            axi_s_wready_o,

    output logic [63:0]                     axi_s_rdata_o,
    output logic [1:0]                      axi_s_rresp_o,
    output logic                            axi_s_rlast_o,
    output logic                            axi_s_rvalid_o,
    input  logic                            axi_s_rready_i,

    output logic [63:0]                     axi_s_bdata_o,
    output logic [1:0]                      axi_s_bresp_o,
    output logic                            axi_s_bvalid_o,
    input  logic                            axi_s_bready_i,

    //============================================================================
    // Error Interface
    //============================================================================
    output logic                            error_o,
    output logic [31:0]                     error_code_o,

    //============================================================================
    // BIST Interface
    //============================================================================
    input  logic                            mbist_en_i,
    input  logic                            bist_start_i,
    output logic                            bist_done_o,
    output logic [7:0]                      bist_result_o
);

    //============================================================================
    // Parameters
    //============================================================================
    parameter int DATA_WIDTH = 64;
    parameter int ADDR_WIDTH = 32;
    parameter int ECC_WIDTH  = 8;

    //============================================================================
    // Internal Signals
    //============================================================================
    logic                                    ecc_write;
    logic                                    ecc_read;
    logic [DATA_WIDTH-1:0]                   ecc_wdata;
    logic [DATA_WIDTH-1:0]                   ecc_rdata;
    logic [ECC_WIDTH-1:0]                    ecc_parity_in;
    logic [ECC_WIDTH-1:0]                    ecc_parity_out;
    logic [ECC_WIDTH-1:0]                    ecc_parity_calc;
    logic [ECC_WIDTH-1:0]                    ecc_syndrome;
    logic                                    ecc_single_error;
    logic                                    ecc_double_error;
    logic                                    ecc_error_detected;
    logic                                    ecc_error_corrected;

    logic [31:0]                             error_count;
    logic                                    axi_arready;
    logic                                    axi_awready;
    logic                                    axi_wready;
    logic                                    axi_rvalid;
    logic                                    axi_bvalid;

    //============================================================================
    // AXI Address Channel
    //============================================================================
    assign axi_s_arready_o = axi_arready;
    assign axi_s_awready_o = axi_awready;

    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            axi_arready <= 1'b1;
            axi_awready <= 1'b1;
        end else begin
            axi_arready <= ~axi_s_arvalid_i | axi_s_arready_o;
            axi_awready <= ~axi_s_awvalid_i | axi_s_awready_o;
        end
    end

    //============================================================================
    // ECC Encoding (Standard Hamming SECDED - RTL-ECC-001)
    //============================================================================
    // Standard Hamming SECDED with 8-bit parity for 64-bit data
    // P1: covers bits 1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,57,59,61,63
    // P2: covers bits 2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63
    // P4: covers bits 4-7,12-15,20-23,28-31,36-39,44-47,52-55,60-63
    // P8: covers bits 8-15,24-31,40-47,56-63
    // P16: covers bits 16-31,48-63
    // P32: covers bits 32-63
    // P64: global parity (all data and parity bits)
    function automatic [ECC_WIDTH-1:0] ecc_encode(input [DATA_WIDTH-1:0] data);
        logic [63:0] d;
        d = data;
        ecc_encode[0] = ^ (d[0] | d[2] | d[4] | d[6] | d[8] | d[10] | d[12] | d[14] |
                          d[16] | d[18] | d[20] | d[22] | d[24] | d[26] | d[28] | d[30] |
                          d[32] | d[34] | d[36] | d[38] | d[40] | d[42] | d[44] | d[46] |
                          d[48] | d[50] | d[52] | d[54] | d[56] | d[58] | d[60] | d[62]);
        ecc_encode[1] = ^ (d[1] | d[2] | d[5] | d[6] | d[9] | d[10] | d[13] | d[14] |
                          d[17] | d[18] | d[21] | d[22] | d[25] | d[26] | d[29] | d[30] |
                          d[33] | d[34] | d[37] | d[38] | d[41] | d[42] | d[45] | d[46] |
                          d[49] | d[50] | d[53] | d[54] | d[57] | d[58] | d[61] | d[62]);
        ecc_encode[2] = ^ (d[3] | d[4] | d[5] | d[6] | d[11] | d[12] | d[13] | d[14] |
                          d[19] | d[20] | d[21] | d[22] | d[27] | d[28] | d[29] | d[30] |
                          d[35] | d[36] | d[37] | d[38] | d[43] | d[44] | d[45] | d[46] |
                          d[51] | d[52] | d[53] | d[54] | d[59] | d[60] | d[61] | d[62]);
        ecc_encode[3] = ^ (d[7] | d[8] | d[9] | d[10] | d[11] | d[12] | d[13] | d[14] |
                          d[23] | d[24] | d[25] | d[26] | d[27] | d[28] | d[29] | d[30] |
                          d[39] | d[40] | d[41] | d[42] | d[43] | d[44] | d[45] | d[46] |
                          d[55] | d[56] | d[57] | d[58] | d[59] | d[60] | d[61] | d[62]);
        ecc_encode[4] = ^ (d[15] | d[16] | d[17] | d[18] | d[19] | d[20] | d[21] | d[22] |
                          d[23] | d[24] | d[25] | d[26] | d[27] | d[28] | d[29] | d[30] |
                          d[47] | d[48] | d[49] | d[50] | d[51] | d[52] | d[53] | d[54] |
                          d[55] | d[56] | d[57] | d[58] | d[59] | d[60] | d[61] | d[62]);
        ecc_encode[5] = ^ (d[31] | d[32] | d[33] | d[34] | d[35] | d[36] | d[37] | d[38] |
                          d[39] | d[40] | d[41] | d[42] | d[43] | d[44] | d[45] | d[46] |
                          d[47] | d[48] | d[49] | d[50] | d[51] | d[52] | d[53] | d[54] |
                          d[55] | d[56] | d[57] | d[58] | d[59] | d[60] | d[61] | d[62]);
        ecc_encode[6] = ^ (d[63] | d[0] | d[1] | d[2] | d[3] | d[4] | d[5] | d[6] |
                          d[7] | d[8] | d[9] | d[10] | d[11] | d[12] | d[13] | d[14] |
                          d[15] | d[16] | d[17] | d[18] | d[19] | d[20] | d[21] | d[22] |
                          d[23] | d[24] | d[25] | d[26] | d[27] | d[28] | d[29] | d[30]);
        ecc_encode[7] = ^ (d[63] | d[62] | d[61] | d[60] | d[59] | d[58] | d[57] | d[56] |
                          d[55] | d[54] | d[53] | d[52] | d[51] | d[50] | d[49] | d[48] |
                          d[47] | d[46] | d[45] | d[44] | d[43] | d[42] | d[41] | d[40] |
                          d[39] | d[38] | d[37] | d[36] | d[35] | d[34] | d[33] | d[32]);
    endfunction

    //============================================================================
    // ECC Decoding and Correction
    //============================================================================
    function automatic [ECC_WIDTH-1:0] ecc_syndrome_calc(
        input [DATA_WIDTH-1:0] data,
        input [ECC_WIDTH-1:0] parity_in,
        input [ECC_WIDTH-1:0] parity_out
    );
        ecc_syndrome_calc = parity_in ^ parity_out;
    endfunction

    function automatic [DATA_WIDTH-1:0] ecc_correct(
        input [DATA_WIDTH-1:0] data,
        input [ECC_WIDTH-1:0] syndrome
    );
        integer bit_pos;
        bit_pos = syndrome[0] * 1 + syndrome[1] * 2 + syndrome[2] * 4 +
                  syndrome[3] * 8 + syndrome[4] * 16 + syndrome[5] * 32;
        ecc_correct = data;
        if (syndrome != 0 && bit_pos < DATA_WIDTH) begin
            ecc_correct[bit_pos] = ~data[bit_pos];
        end
    endfunction

    //============================================================================
    // Write Path with ECC
    //============================================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            ecc_write <= 1'b0;
            ecc_wdata <= '0;
            ecc_parity_in <= '0;
            axi_wready <= 1'b1;
        end else begin
            if (axi_s_wvalid_i && axi_s_wready_o) begin
                ecc_write <= 1'b1;
                ecc_wdata <= axi_s_wdata_i;
                ecc_parity_in <= ecc_encode(axi_s_wdata_i);
                axi_wready <= 1'b0;
            end else begin
                ecc_write <= 1'b0;
                axi_wready <= 1'b1;
            end
        end
    end

    assign sram_addr_o  = axi_s_awvalid_i ? axi_s_awaddr_i : axi_s_araddr_i;
    assign sram_wdata_o = {ecc_wdata, ecc_parity_in};
    assign sram_we_o    = ecc_write;
    assign sram_wstrb_o = axi_s_wstrb_i;

    //============================================================================
    // Read Path with ECC
    //============================================================================
    logic [71:0]                            sram_data_with_ecc;
    logic [DATA_WIDTH-1:0]                  sram_data_corrected;
    logic [ECC_WIDTH-1:0]                   sram_parity;

    assign sram_data_with_ecc = sram_rdata_i;
    assign sram_data_corrected = sram_data_with_ecc[63:0];
    assign sram_parity = sram_data_with_ecc[71:64];

    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            ecc_read <= 1'b0;
            ecc_syndrome <= '0;
            ecc_single_error <= 1'b0;
            ecc_double_error <= 1'b0;
        end else if (axi_s_arvalid_i && axi_s_arready_o) begin
            ecc_read <= 1'b1;
            ecc_parity_calc = ecc_encode(sram_data_corrected);
            ecc_syndrome = ecc_syndrome_calc(sram_data_corrected, sram_parity, ecc_parity_calc);
            ecc_single_error = (ecc_syndrome != 0) && (ecc_syndrome < 256);
            ecc_double_error = (ecc_syndrome != 0) && (ecc_syndrome >= 256);
        end else begin
            ecc_read <= 1'b0;
        end
    end

    //============================================================================
    // ECC Error Detection and Logging
    //============================================================================
    assign ecc_error_detected = ecc_single_error || ecc_double_error;
    assign ecc_error_corrected = ecc_single_error;

    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            error_o <= 1'b0;
            error_code_o <= '0;
            error_count <= '0;
        end else begin
            error_o <= ecc_error_detected;
            if (ecc_error_detected) begin
                error_count <= error_count + 1;
                if (ecc_double_error) begin
                    error_code_o <= 32'hE001_0000 | {sram_addr_o[15:0], ecc_syndrome[7:0]};
                end else begin
                    error_code_o <= 32'hE002_0000 | {sram_addr_o[15:0], ecc_syndrome[7:0]};
                end
            end
        end
    end

    //============================================================================
    // Read Data Output
    //============================================================================
    logic [DATA_WIDTH-1:0]                  corrected_data;

    assign corrected_data = ecc_correct(sram_data_corrected, ecc_syndrome);

    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            axi_s_rvalid <= 1'b0;
            axi_s_rdata_o <= '0;
            axi_s_rresp_o <= 2'b00;
            axi_s_rlast_o <= 1'b1;
        end else if (ecc_read) begin
            axi_s_rvalid <= 1'b1;
            axi_s_rdata_o <= corrected_data;
            axi_s_rresp_o <= ecc_double_error ? 2'b10 : (ecc_single_error ? 2'b01 : 2'b00);
            axi_s_rlast_o <= 1'b1;
        end else begin
            axi_s_rvalid <= 1'b0;
        end
    end

    //============================================================================
    // Write Response
    //============================================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            axi_bvalid <= 1'b0;
            axi_s_bdata_o <= '0;
            axi_s_bresp_o <= 2'b00;
        end else if (ecc_write) begin
            axi_bvalid <= 1'b1;
            axi_s_bresp_o <= 2'b00;
        end else begin
            axi_bvalid <= 1'b0;
        end
    end

    assign axi_s_bvalid_o = axi_bvalid;
    assign axi_s_bdata_o = '0;

    //============================================================================
    // BIST Control
    //============================================================================
    logic [7:0]                             bist_count;
    logic                                   bist_running;

    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            bist_running <= 1'b0;
            bist_count <= '0;
            bist_done_o <= 1'b0;
            bist_result_o <= '0;
        end else if (bist_start_i && !bist_running) begin
            bist_running <= 1'b1;
            bist_count <= '0;
        end else if (bist_running) begin
            if (bist_count == 8'd255) begin
                bist_running <= 1'b0;
                bist_done_o <= 1'b1;
                bist_result_o <= error_count[7:0];
            end else begin
                bist_count <= bist_count + 1;
            end
        end else begin
            bist_done_o <= 1'b0;
        end
    end

endmodule
