//=============================================================================
// Cortex-R52 Core Wrapper (Simplified for Integration)
//=============================================================================

`timescale 1ns/1ps

module cortex_r52_core (
    input  logic                            clk_i,
    input  logic                            rst_n_i,
    input  logic                            scan_en_i,
    input  logic [31:0]                     base_addr_i,

    output logic [31:0]                     axi_araddr_o,
    output logic [7:0]                      axi_arlen_o,
    output logic [2:0]                      axi_arsize_o,
    output logic [1:0]                      axi_arburst_o,
    output logic                            axi_arvalid_o,
    input  logic                            axi_arready_i,

    output logic [31:0]                     axi_awaddr_o,
    output logic [7:0]                      axi_awlen_o,
    output logic [2:0]                      axi_awsize_o,
    output logic [1:0]                      axi_awburst_o,
    output logic                            axi_awvalid_o,
    input  logic                            axi_awready_i,

    output logic [63:0]                     axi_wdata_o,
    output logic [7:0]                      axi_wstrb_o,
    output logic                            axi_wlast_o,
    output logic                            axi_wvalid_o,
    input  logic                            axi_wready_i,

    input  logic [63:0]                     axi_rdata_i,
    input  logic [1:0]                      axi_rresp_i,
    input  logic                            axi_rlast_i,
    input  logic                            axi_rvalid_i,
    output logic                            axi_rready_o,

    input  logic [63:0]                     axi_bdata_i,
    input  logic [1:0]                      axi_bresp_i,
    input  logic                            axi_bvalid_i,
    output logic                            axi_bready_o,

    output logic [63:0]                     rdata_o,
    output logic [1:0]                      rresp_o,
    output logic                            rvalid_o,
    output logic                            rlast_o
);

    assign axi_arsize_o  = 3'b011;  // 64-bit
    assign axi_arburst_o = 2'b01;   // INCR
    assign axi_awsize_o  = 3'b011;  // 64-bit
    assign axi_awburst_o = 2'b01;   // INCR

    logic [31:0]                             pc;
    logic                                    fetch_enable;

    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            pc <= base_addr_i;
            fetch_enable <= 1'b0;
        end else if (rst_n_i && (pc == base_addr_i)) begin
            pc <= base_addr_i + 32'h100;
            fetch_enable <= 1'b1;
        end else if (fetch_enable) begin
            if (axi_arready_i && axi_arvalid_o) begin
                pc <= pc + 32'h8;
            end
        end
    end

    assign axi_araddr_o  = pc;
    assign axi_arlen_o   = 8'd0;
    assign axi_arvalid_o = fetch_enable;
    assign axi_awaddr_o  = pc;
    assign axi_awlen_o   = 8'd0;
    assign axi_awvalid_o = 1'b0;

    assign axi_wdata_o   = '0;
    assign axi_wstrb_o   = '0;
    assign axi_wlast_o   = 1'b0;
    assign axi_wvalid_o  = 1'b0;

    assign axi_rready_o  = 1'b1;
    assign axi_bready_o  = 1'b1;

    always_ff @(posedge clk_i) begin
        if (axi_rvalid_i) begin
            rdata_o  <= axi_rdata_i;
            rresp_o  <= axi_rresp_i;
            rvalid_o <= axi_rvalid_i;
            rlast_o  <= axi_rlast_i;
        end else begin
            rvalid_o <= 1'b0;
        end
    end

endmodule
