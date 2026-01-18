//-----------------------------------------------------------------------------
// File: dma_controller.sv
// Description: Ethernet DMA Controller with Scatter-Gather
// Author: YaoGuang SoC Team
// Date: 2026-01-19
//-----------------------------------------------------------------------------

`timescale 1ps/1ps

module dma_controller #(
    parameter PORT_ID = 0,
    parameter CHANNEL_ID = 0,
    parameter AXI_DATA_WIDTH = 256
) (
    input  logic                                clk_sys,
    input  logic                                rst_n_sys,
    output logic                                tx_req,
    input  logic                                tx_done,
    output logic                                rx_req,
    input  logic                                rx_done,
    output logic                                dma_err,
    output logic [AXI_ADDR_WIDTH-1:0]           s_axibus_awaddr,
    output logic [7:0]                          s_axibus_awlen,
    output logic                                s_axibus_awvalid,
    input  logic                                s_axibus_awready,
    output logic [AXI_DATA_WIDTH-1:0]           s_axibus_wdata,
    output logic [(AXI_DATA_WIDTH/8)-1:0]       s_axibus_wstrb,
    output logic                                s_axibus_wlast,
    output logic                                s_axibus_wvalid,
    input  logic                                s_axibus_wready,
    input  logic [1:0]                          s_axibus_bresp,
    input  logic                                s_axibus_bvalid,
    output logic                                s_axibus_bready,
    output logic [AXI_ADDR_WIDTH-1:0]           s_axibus_araddr,
    output logic [7:0]                          s_axibus_arlen,
    output logic                                s_axibus_arvalid,
    input  logic                                s_axibus_arready,
    input  logic [AXI_DATA_WIDTH-1:0]           s_axibus_rdata,
    input  logic                                s_axibus_rvalid,
    input  logic                                s_axibus_rlast
);

    localparam DESC_COUNT = 16;
    localparam DESC_SIZE = 32;

    // Descriptor Structure
    typedef struct packed {
        logic [63:0]                                 addr;
        logic [31:0]                                 length;
        logic [15:0]                                 reserved;
        logic                                        ioc;
        logic                                        ls;
        logic                                        fs;
        logic [2:0]                                  control;
        logic                                        owner;
    } desc_t;

    // Descriptor Ring
    desc_t                                       tx_desc_ring [0:DESC_COUNT-1];
    desc_t                                       rx_desc_ring [0:DESC_COUNT-1];
    logic [5:0]                                  tx_desc_head;
    logic [5:0]                                  tx_desc_tail;
    logic [5:0]                                  rx_desc_head;
    logic [5:0]                                  rx_desc_tail;

    // Current Descriptor
    desc_t                                       curr_tx_desc;
    desc_t                                       curr_rx_desc;
    logic                                        curr_tx_desc_valid;
    logic                                        curr_rx_desc_valid;

    // DMA State Machine
    typedef enum logic [3:0] {
        DMA_IDLE,
        DMA_DESC_FETCH,
        DMA_DATA_XFER,
        DMA_DESC_UPDATE,
        DMA_COMPLETE,
        DMA_ERROR
    } dma_state_t;

    dma_state_t                                  tx_dma_state;
    dma_state_t                                  rx_dma_state;

    // Transfer Counters
    logic [31:0]                                 bytes_transferred;
    logic                                        desc_error;
    logic                                        bus_error;

    // AXI Control
    logic                                        axibus_idle;
    logic [3:0]                                  axibus_awid;
    logic [AXI_ADDR_WIDTH-1:0]                   axibus_awaddr;
    logic [7:0]                                  axibus_awlen;
    logic [1:0]                                  axibus_awburst;
    logic                                        axibus_awvalid;
    logic                                        axibus_awready;

    logic [AXI_DATA_WIDTH-1:0]                   axibus_wdata;
    logic [(AXI_DATA_WIDTH/8)-1:0]               axibus_wstrb;
    logic                                        axibus_wlast;
    logic                                        axibus_wvalid;
    logic                                        axibus_wready;

    logic [1:0]                                  axibus_bresp;
    logic                                        axibus_bvalid;
    logic                                        axibus_bready;

    // TX DMA
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            tx_dma_state <= DMA_IDLE;
            tx_desc_head <= '0;
            tx_desc_tail <= '0;
            tx_req <= 1'b0;
            s_axibus_arvalid <= 1'b0;
        end else begin
            case (tx_dma_state)
                DMA_IDLE: begin
                    if (tx_desc_head != tx_desc_tail) begin
                        tx_req <= 1'b1;
                        tx_dma_state <= DMA_DESC_FETCH;
                    end
                end
                DMA_DESC_FETCH: begin
                    s_axibus_araddr <= tx_desc_ring[tx_desc_head].addr;
                    s_axibus_arlen <= 8'd3;
                    s_axibus_arvalid <= 1'b1;
                    if (s_axibus_arready && s_axibus_rvalid) begin
                        curr_tx_desc <= s_axibus_rdata[31:0];
                        tx_desc_head <= tx_desc_head + 1;
                        tx_dma_state <= DMA_DATA_XFER;
                    end
                end
                DMA_DATA_XFER: begin
                    if (tx_done) begin
                        bytes_transferred <= curr_tx_desc.length;
                        tx_dma_state <= DMA_DESC_UPDATE;
                    end else if (bus_error || desc_error) begin
                        tx_dma_state <= DMA_ERROR;
                    end
                end
                DMA_DESC_UPDATE: begin
                    s_axibus_awaddr <= tx_desc_ring[tx_desc_head].addr + 8;
                    s_axibus_wdata <= {curr_tx_desc.length, 24'b0};
                    s_axibus_wstrb <= '1;
                    s_axibus_wlast <= 1'b1;
                    s_axibus_awvalid <= 1'b1;
                    s_axibus_wvalid <= 1'b1;
                    if (s_axibus_awready && s_axibus_wready) begin
                        tx_desc_tail <= tx_desc_tail + 1;
                        tx_req <= 1'b0;
                        tx_dma_state <= DMA_IDLE;
                    end
                end
                DMA_ERROR: begin
                    dma_err <= 1'b1;
                    tx_req <= 1'b0;
                    tx_dma_state <= DMA_IDLE;
                end
            endcase
        end
    end

    // RX DMA
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            rx_dma_state <= DMA_IDLE;
            rx_desc_head <= '0;
            rx_desc_tail <= '0;
            rx_req <= 1'b0;
        end else begin
            case (rx_dma_state)
                DMA_IDLE: begin
                    if (rx_desc_head != rx_desc_tail) begin
                        rx_req <= 1'b1;
                        rx_dma_state <= DMA_DESC_FETCH;
                    end
                end
                DMA_DESC_FETCH: begin
                    s_axibus_araddr <= rx_desc_ring[rx_desc_head].addr;
                    s_axibus_arlen <= 8'd3;
                    s_axibus_arvalid <= 1'b1;
                    if (s_axibus_arready && s_axibus_rvalid) begin
                        curr_rx_desc <= s_axibus_rdata[31:0];
                        rx_desc_head <= rx_desc_head + 1;
                        rx_dma_state <= DMA_DATA_XFER;
                    end
                end
                DMA_DATA_XFER: begin
                    if (rx_done) begin
                        bytes_transferred <= curr_rx_desc.length;
                        rx_dma_state <= DMA_DESC_UPDATE;
                    end else if (bus_error || desc_error) begin
                        rx_dma_state <= DMA_ERROR;
                    end
                end
                DMA_DESC_UPDATE: begin
                    s_axibus_awaddr <= rx_desc_ring[rx_desc_head].addr + 8;
                    s_axibus_wdata <= {bytes_transferred, 24'b0};
                    s_axibus_wstrb <= '1;
                    s_axibus_wlast <= 1'b1;
                    s_axibus_awvalid <= 1'b1;
                    s_axibus_wvalid <= 1'b1;
                    if (s_axibus_awready && s_axibus_wready) begin
                        rx_desc_tail <= rx_desc_tail + 1;
                        rx_req <= 1'b0;
                        rx_dma_state <= DMA_IDLE;
                    end
                end
                DMA_ERROR: begin
                    dma_err <= 1'b1;
                    rx_req <= 1'b0;
                    rx_dma_state <= DMA_IDLE;
                end
            endcase
        end
    end

    // Descriptor Ring Base Address
    logic [63:0]                                 tx_desc_base;
    logic [63:0]                                 rx_desc_base;
    logic [31:0]                                 desc_ring_size;

    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            tx_desc_base <= '0;
            rx_desc_base <= '0;
            desc_ring_size <= 32'dDESC_COUNT;
        end else begin
            if (s_axibus_awvalid && s_axibus_awready) begin
                if (s_axibus_awaddr[11:8] == 4'h0) begin
                    tx_desc_base <= s_axibus_wdata[63:0];
                end
                if (s_axibus_awaddr[11:8] == 4'h1) begin
                    rx_desc_base <= s_axibus_wdata[63:0];
                end
            end
        end
    end

endmodule
