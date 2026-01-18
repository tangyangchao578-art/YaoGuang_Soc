//-----------------------------------------------------------------------------
// Tensor Buffer (SRAM Wrapper)
// File: tensor_buffer.sv
// Description: Multi-bank SRAM for Tensor Storage
//              Supports read/write, ECC, and power gating
//-----------------------------------------------------------------------------
// User: NPU RTL Design Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------

`timescale 1ns/1ps

module tensor_buffer #
(
    parameter int SIZE           = 2097152,
    parameter int DATA_WIDTH     = 512,
    parameter int ADDR_WIDTH     = 16,
    parameter int NUM_BANKS      = 16,
    parameter bit ECC_ENABLE     = 1'b1
)
(
    // Clock and Reset
    input  logic                  clk_i,
    input  logic                  rst_ni,

    // SRAM Interface
    input  logic                  we_i,           // Write enable (active low)
    input  logic [ADDR_WIDTH-1:0] addr_i,
    input  logic [DATA_WIDTH-1:0] wdata_i,
    input  logic [DATA_WIDTH/8-1:0] wmask_i,    // Byte enable
    output logic [DATA_WIDTH-1:0] rdata_o,

    // Power Management
    input  logic                  power_gate_i,   // Power gate control
    output logic                  power_ok_o,     // Power good indicator

    // ECC Status
    output logic                  ecc_error_o,    // Single-bit error detected
    output logic                  ecc_uncorrectable_o, // Multi-bit error
    output logic [7:0]            ecc_err_count_o // Error counter
);

    //-------------------------------------------------------------------------
    // Parameters
    //-------------------------------------------------------------------------
    localparam int BANK_SIZE      = SIZE / NUM_BANKS;
    localparam int BANK_ADDR      = $clog2(BANK_SIZE);
    localparam int BYTE_WIDTH     = 8;
    localparam int BYTE_COUNT     = DATA_WIDTH / BYTE_WIDTH;

    //-------------------------------------------------------------------------
    // Signals
    //-------------------------------------------------------------------------
    // Bank signals
    logic [DATA_WIDTH-1:0]        bank_wdata [NUM_BANKS-1:0];
    logic [DATA_WIDTH/8-1:0]      bank_wmask [NUM_BANKS-1:0];
    logic [BANK_ADDR-1:0]         bank_addr [NUM_BANKS-1:0];
    logic                         bank_we [NUM_BANKS-1:0];
    logic [DATA_WIDTH-1:0]        bank_rdata [NUM_BANKS-1:0];

    // ECC signals
    logic [DATA_WIDTH-1:0]        ecc_encoded_wdata;
    logic [DATA_WIDTH-1:0]        ecc_encoded_rdata;
    logic [7:0]                   ecc_syndrome;
    logic                         ecc_single_err;
    logic                         ecc_double_err;
    logic [DATA_WIDTH-1:0]        ecc_corrected_data;

    // Power management
    logic                         bank_power_en [NUM_BANKS-1:0];
    logic                         all_banks_ready;

    // Error tracking
    logic [7:0]                   error_counter;

    //-------------------------------------------------------------------------
    // Bank Address Decoder
    //-------------------------------------------------------------------------
    generate
        for (genvar i = 0; i < NUM_BANKS; i++) begin : GEN_BANK_DECODE
            assign bank_we[i] = we_i;
            assign bank_addr[i] = addr_i[BANK_ADDR-1:0];
            assign bank_wdata[i] = wdata_i;
            assign bank_wmask[i] = wmask_i;
        end
    endgenerate

    //-------------------------------------------------------------------------
    // SRAM Banks
    //-------------------------------------------------------------------------
    generate
        for (genvar i = 0; i < NUM_BANKS; i++) begin : GEN_SRAM_BANKS
            sram_512x16k #(
                .DATA_WIDTH       (DATA_WIDTH),
                .ADDR_WIDTH       (BANK_ADDR),
                .ECC_ENABLE       (ECC_ENABLE)
            ) u_sram_bank (
                .clk_i            (clk_i),
                .rst_ni           (rst_ni),
                .we_i             (bank_we[i]),
                .addr_i           (bank_addr[i]),
                .wdata_i          (bank_wdata[i]),
                .wmask_i          (bank_wmask[i]),
                .rdata_o          (bank_rdata[i]),
                .ecc_error_o      (),
                .ecc_uncorrectable_o ()
            );
        end
    endgenerate

    //-------------------------------------------------------------------------
    // Output Multiplexer
    //-------------------------------------------------------------------------
    assign rdata_o = bank_rdata[0];

    //-------------------------------------------------------------------------
    // ECC Encoder/Decoder (if enabled)
    //-------------------------------------------------------------------------
    generate
        if (ECC_ENABLE) begin : GEN_ECC
            ecc_64bit #(
                .DATA_WIDTH       (DATA_WIDTH)
            ) u_ecc (
                .clk_i            (clk_i),
                .rst_ni           (rst_ni),
                .wdata_i          (wdata_i),
                .rdata_i          (bank_rdata[0]),
                .wdata_o          (ecc_encoded_wdata),
                .rdata_o          (ecc_encoded_rdata),
                .syndrome_o       (ecc_syndrome),
                .single_err_o     (ecc_single_err),
                .double_err_o     (ecc_double_err),
                .corrected_rdata_o (ecc_corrected_data)
            );

            // Error counting
            always_ff @(posedge clk_i or negedge rst_ni) begin
                if (!rst_ni) begin
                    error_counter <= '0;
                end else if (ecc_single_err || ecc_double_err) begin
                    error_counter <= error_counter + 1;
                end
            end

            // Error outputs
            assign ecc_error_o = ecc_single_err;
            assign ecc_uncorrectable_o = ecc_double_err;
            assign ecc_err_count_o = error_counter;

        end else begin : NO_ECC
            assign ecc_error_o = 1'b0;
            assign ecc_uncorrectable_o = 1'b0;
            assign ecc_err_count_o = '0;
        end
    endgenerate

    //-------------------------------------------------------------------------
    // Power Management
    //-------------------------------------------------------------------------
    generate
        for (genvar i = 0; i < NUM_BANKS; i++) begin : GEN_POWER
            always_ff @(posedge clk_i) begin
                bank_power_en[i] <= ~power_gate_i;
            end
        end
    endgenerate

    assign power_ok_o = all_banks_ready;

endmodule

//-----------------------------------------------------------------------------
// Internal SRAM Module (512-bit wide, 16K depth)
//-----------------------------------------------------------------------------
module sram_512x16k #
(
    parameter int DATA_WIDTH     = 512,
    parameter int ADDR_WIDTH     = 14,
    parameter bit ECC_ENABLE     = 1'b1
)
(
    input  logic                  clk_i,
    input  logic                  rst_ni,
    input  logic                  we_i,
    input  logic [ADDR_WIDTH-1:0] addr_i,
    input  logic [DATA_WIDTH-1:0] wdata_i,
    input  logic [DATA_WIDTH/8-1:0] wmask_i,
    output logic [DATA_WIDTH-1:0] rdata_o,
    output logic                  ecc_error_o,
    output logic                  ecc_uncorrectable_o
);

    //-------------------------------------------------------------------------
    // Memory Array
    //-------------------------------------------------------------------------
    (* ram_style = "block" *)
    logic [DATA_WIDTH-1:0]        mem [(1<<ADDR_WIDTH)-1:0];

    //-------------------------------------------------------------------------
    // Write Operation
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i) begin
        if (!we_i) begin
            for (int i = 0; i < DATA_WIDTH/8; i++) begin
                if (wmask_i[i]) begin
                    mem[addr_i][i*8+:8] <= wdata_i[i*8+:8];
                end
            end
        end
    end

    //-------------------------------------------------------------------------
    // Read Operation
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i) begin
        rdata_o <= mem[addr_i];
    end

    //-------------------------------------------------------------------------
    // ECC Placeholder (simplified)
    //-------------------------------------------------------------------------
    assign ecc_error_o = 1'b0;
    assign ecc_uncorrectable_o = 1'b0;

endmodule

//-----------------------------------------------------------------------------
// ECC Encoder/Decoder (64-bit with SECDED)
//-----------------------------------------------------------------------------
module ecc_64bit #
(
    parameter int DATA_WIDTH     = 512
)
(
    input  logic                  clk_i,
    input  logic                  rst_ni,
    input  logic [DATA_WIDTH-1:0] wdata_i,
    input  logic [DATA_WIDTH-1:0] rdata_i,
    output logic [DATA_WIDTH-1:0] wdata_o,
    output logic [DATA_WIDTH-1:0] rdata_o,
    output logic [7:0]            syndrome_o,
    output logic                  single_err_o,
    output logic                  double_err_o,
    output logic [DATA_WIDTH-1:0] corrected_rdata_o
);

    // Simplified ECC (placeholder for full implementation)
    assign wdata_o = wdata_i;
    assign rdata_o = rdata_i;
    assign syndrome_o = '0;
    assign single_err_o = 1'b0;
    assign double_err_o = 1'b0;
    assign corrected_rdata_o = rdata_i;

endmodule
