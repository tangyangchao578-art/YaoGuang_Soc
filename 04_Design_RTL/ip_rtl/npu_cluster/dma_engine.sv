//-----------------------------------------------------------------------------
// DMA Engine
// File: dma_engine.sv
// Description: AXI4 DMA Engine for NPU Cluster
//              Handles data transfer between NoC and local SRAM
//-----------------------------------------------------------------------------
// User: NPU RTL Design Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------

`timescale 1ns/1ps

module dma_engine #
(
    parameter int ID_WIDTH       = 8,
    parameter int ADDR_WIDTH     = 32,
    parameter int DATA_WIDTH     = 512,
    parameter int BURST_LEN      = 16
)
(
    // Clock and Reset
    input  logic                  clk_i,
    input  logic                  rst_ni,

    // AXI4 Read Channel
    input  logic [DATA_WIDTH-1:0] noc_rdata_i,
    input  logic                  noc_rvalid_i,
    output logic [ID_WIDTH-1:0]   noc_rid_o,
    output logic [ADDR_WIDTH-1:0] noc_araddr_o,
    output logic [7:0]            noc_arlen_o,
    output logic [2:0]            noc_arsize_o,
    output logic [1:0]            noc_arburst_o,
    output logic                  noc_arvalid_o,
    input  logic                  noc_arready_i,

    // AXI4 Write Channel
    output logic [DATA_WIDTH-1:0] noc_wdata_o,
    output logic [DATA_WIDTH/8-1:0] noc_wstrb_o,
    output logic                  noc_wvalid_o,
    input  logic                  noc_wready_i,
    output logic [ID_WIDTH-1:0]   noc_awid_o,
    output logic [ADDR_WIDTH-1:0] noc_awaddr_o,
    output logic [7:0]            noc_awlen_o,
    output logic [2:0]            noc_awsize_o,
    output logic [1:0]            noc_awburst_o,
    output logic                  noc_awvalid_o,
    input  logic                  noc_awready_i,
    input  logic                  noc_bvalid_i,
    input  logic [ID_WIDTH-1:0]   noc_bid_i,

    // Request Interface
    input  logic                  req_i,
    input  logic [ADDR_WIDTH-1:0] src_addr_i,
    input  logic [ADDR_WIDTH-1:0] dst_addr_i,
    input  logic [21:0]           size_i,        // Transfer size in bytes
    input  logic [2:0]            op_i,          // 000: Mem to Reg, 001: Reg to Mem, 010: Mem to Mem
    output logic                  done_o,
    output logic                  error_o,

    // Local Memory Interface
    output logic                  local_we_o,
    output logic [ADDR_WIDTH-1:0] local_addr_o,
    output logic [DATA_WIDTH-1:0] local_wdata_o,
    input  logic [DATA_WIDTH-1:0] local_rdata_i
);

    //-------------------------------------------------------------------------
    // Parameters
    //-------------------------------------------------------------------------
    localparam int BEAT_SIZE      = DATA_WIDTH / 8;
    localparam int BURST_BEATS    = BURST_LEN;

    //-------------------------------------------------------------------------
    // Signals
    //-------------------------------------------------------------------------
    // State machine
    typedef enum logic [3:0] {
        DMA_IDLE,
        DMA_AR_FIRE,
        DMA_R_WAIT,
        DMA_R_DATA,
        DMA_AW_FIRE,
        DMA_W_DATA,
        DMA_W_WAIT,
        DMA_COMPLETE,
        DMA_ERROR
    } dma_state_t;

    dma_state_t                  state;
    dma_state_t                  next_state;

    // Counters
    logic [21:0]                 bytes_remaining;
    logic [7:0]                  beats_remaining;
    logic [21:0]                 bytes_transferred;

    // Address tracking
    logic [ADDR_WIDTH-1:0]       current_src_addr;
    logic [ADDR_WIDTH-1:0]       current_dst_addr;

    // Data buffer
    logic [DATA_WIDTH-1:0]       read_buffer;
    logic                        buffer_valid;

    // Error handling
    logic [3:0]                  error_code;
    logic                        resp_error;

    //-------------------------------------------------------------------------
    // State Machine
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            state <= DMA_IDLE;
        end else begin
            state <= next_state;
        end
    end

    always_comb begin
        next_state = state;

        case (state)
            DMA_IDLE: begin
                if (req_i) begin
                    current_src_addr = src_addr_i;
                    current_dst_addr = dst_addr_i;
                    bytes_remaining  = size_i;
                    bytes_transferred = '0;

                    if (op_i == 3'b000) begin // Mem to Reg (Read)
                        next_state = DMA_AR_FIRE;
                    end else if (op_i == 3'b001) begin // Reg to Mem (Write)
                        next_state = DMA_AW_FIRE;
                    end else begin // Mem to Mem
                        next_state = DMA_AR_FIRE;
                    end
                end
            end

            DMA_AR_FIRE: begin
                if (noc_arready_i && noc_arvalid_o) begin
                    next_state = DMA_R_WAIT;
                end
            end

            DMA_R_WAIT: begin
                if (noc_rvalid_i) begin
                    read_buffer = noc_rdata_i;
                    buffer_valid = 1'b1;

                    if (op_i == 3'b000) begin // Mem to Reg
                        next_state = DMA_COMPLETE;
                    end else begin // Mem to Mem
                        next_state = DMA_AW_FIRE;
                    end
                end
            end

            DMA_AW_FIRE: begin
                if (noc_awready_i && noc_awvalid_o) begin
                    next_state = DMA_W_DATA;
                end
            end

            DMA_W_DATA: begin
                if (noc_wready_i && noc_wvalid_o) begin
                    bytes_transferred = bytes_transferred + BEAT_SIZE;
                    bytes_remaining = bytes_remaining - BEAT_SIZE;

                    if (bytes_remaining <= BEAT_SIZE) begin
                        next_state = DMA_W_WAIT;
                    end
                end
            end

            DMA_W_WAIT: begin
                if (noc_bvalid_i) begin
_error) begin
                    if (resp                        next_state = DMA_ERROR;
                    end else if (bytes_remaining > BEAT_SIZE) begin
                        next_state = DMA_AW_FIRE;
                    end else begin
                        next_state = DMA_COMPLETE;
                    end
                end
            end

            DMA_COMPLETE: begin
                next_state;
            end

 = DMA_IDLE            DMA_ERROR: begin
                if (error_code[0]) begin
                    next_state = DMA_IDLE;
                end
            end

            default: begin
                next_state = DMA_IDLE;
            end
        endcase
    end

    //-------------------------------------------------------------------------
    // AXI Read Address Channel
    //-------------------------------------------------------------------------
    assign noc_arvalid_o = (state == DMA_AR_FIRE);
    assign noc_araddr_o  = current_src_addr;
    assign noc_arlen_o   = (bytes_remaining > 256) ? 8'd15 : (bytes_remaining[8:0] - 1);
    assign noc_arsize_o  = 3'd6; // 64 bytes per beat (512-bit)
    assign noc_arburst_o = 2'b01; // INCR
    assign noc_rid_o     = '0;

    //-------------------------------------------------------------------------
    // AXI Write Address Channel
    //-------------------------------------------------------------------------
    assign noc_awvalid_o = (state == DMA_AW_FIRE);
    assign noc_awaddr_o  = current_dst_addr;
    assign noc_awlen_o   = (bytes_remaining > 256) ? 8'd15 : (bytes_remaining[8:0] - 1);
    assign noc_awsize_o  = 3'd6; // 64 bytes per beat (512-bit)
    assign noc_awburst_o = 2'b01; // INCR
    assign noc_awid_o    = '0;

    //-------------------------------------------------------------------------
    // AXI Write Data Channel
    //-------------------------------------------------------------------------
    assign noc_wvalid_o  = (state == DMA_W_DATA);
    assign noc_wdata_o   = read_buffer;
    assign noc_wstrb_o   = {DATA_WIDTH/8{1'b1}}; // All bytes valid

    //-------------------------------------------------------------------------
    // AXI Response Channel
    //-------------------------------------------------------------------------
    assign resp_error = noc_bvalid_i && (noc_bid_i != '0);

    //-------------------------------------------------------------------------
    // Local Memory Interface
    //-------------------------------------------------------------------------
    assign local_we_o    = (state == DMA_W_DATA) && noc_wvalid_o;
    assign local_addr_o  = current_dst_addr;
    assign local_wdata_o = read_buffer;

    //-------------------------------------------------------------------------
    // Status Outputs
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            done_o   <= 1'b0;
            error_o  <= 1'b0;
        end else begin
            done_o   <= (state == DMA_COMPLETE);
            error_o  <= (state == DMA_ERROR);
        end
    end

    //-------------------------------------------------------------------------
    // Address Increment
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i) begin
        if (noc_arvalid_o && noc_arready_i) begin
            current_src_addr <= current_src_addr + BURST_BEATS * BEAT_SIZE;
        end
        if (noc_awvalid_o && noc_awready_i) begin
            current_dst_addr <= current_dst_addr + BURST_BEATS * BEAT_SIZE;
        end
    end

    //-------------------------------------------------------------------------
    // Error Detection
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i) begin
        if (noc_bvalid_i) begin
            if (noc_bid_i != '0) begin
                error_code <= 4'b0001;
            end
        end
        if (noc_rvalid_i && noc_rid_o != '0) begin
            error_code <= 4'b0010;
        end
    end

endmodule
