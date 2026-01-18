// -----------------------------------------------------------------------------
// File: framebuffer_reader.sv
// Description: Framebuffer Reader - AXI Master for Pixel Data Fetch
// Author: YaoGuang SoC Design Team
// Date: 2026-01-18
// -----------------------------------------------------------------------------

`timescale 1ns/1ps

module framebuffer_reader #(
    parameter integer AXI_DATA_WIDTH = 64,
    parameter integer AXI_ADDR_WIDTH = 32
) (
    input  logic                                    pixel_clk,
    input  logic                                    rst_n,
    input  logic                                    frame_start,
    input  logic [AXI_ADDR_WIDTH-1:0]              fb_base_addr,
    input  logic [31:0]                             fb_stride,
    input  logic [7:0]                              pixel_format,
    input  logic [11:0]                             pixel_x,
    input  logic [11:0]                             pixel_y,
    output logic                                    pixel_valid,
    output logic [31:0]                             pixel_data_r,
    output logic [31:0]                             pixel_data_g,
    output logic [31:0]                             pixel_data_b,

    // AXI Master Interface
    output logic [AXI_ADDR_WIDTH-1:0]              m_araddr,
    output logic [7:0]                             m_arlen,
    output logic [2:0]                             m_arsize,
    output logic [1:0]                             m_arburst,
    output logic                                    m_arvalid,
    input  logic                                    m_arready,
    input  logic [AXI_DATA_WIDTH-1:0]              m_rdata,
    input  logic [1:0]                             m_rresp,
    input  logic                                    m_rvalid,
    output logic                                    m_rready
);

    // FIFO Depth for Pixel Data
    localparam integer FIFO_DEPTH = 16;
    localparam integer FIFO_WIDTH = 64;

    // Pixel Format Encoding
    localparam [3:0] FMT_RGB888  = 4'd0;
    localparam [3:0] FMT_RGB565  = 4'd1;
    localparam [3:0] FMT_RGBA8888 = 4'd2;
    localparam [3:0] FMT_YUV422  = 4'd4;
    localparam [3:0] FMT_YUV420  = 4'd5;

    // Registers
    logic [AXI_ADDR_WIDTH-1:0]                     read_addr;
    logic [9:0]                                    read_count;
    logic [3:0]                                    state_reg, state_next;
    logic [7:0]                                    pixels_in_line;
    logic [AXI_ADDR_WIDTH-1:0]                     line_base_addr;

    // FIFO Signals
    logic                                          fifo_wr_en;
    logic [FIFO_WIDTH-1:0]                         fifo_wr_data;
    logic                                          fifo_full;
    logic                                          fifo_rd_en;
    logic [FIFO_WIDTH-1:0]                         fifo_rd_data;
    logic                                          fifo_empty;
    logic [5:0]                                    fifo_count;

    // Pixel Buffer
    logic [7:0]                                    pixel_buffer [0:7];
    logic [2:0]                                    pixel_index;
    logic                                          buffer_valid;

    // FSM State Definition
    typedef enum logic [3:0] {
        IDLE        = 4'd0,
        FETCH_LINE  = 4'd1,
        WAIT_DATA   = 4'd2,
        PARSE_PIXEL = 4'd3,
        DONE        = 4'd4
    } state_t;

    // -------------------------------------------------------------------------
    // AXI Read Controller
    // -------------------------------------------------------------------------
    always_ff @(posedge pixel_clk or negedge rst_n) begin
        if (!rst_n) begin
            m_arvalid <= 1'b0;
            m_rready  <= 1'b0;
        end else begin
            case (state_reg)
                IDLE: begin
                    if (frame_start) begin
                        m_arvalid <= 1'b1;
                        read_addr <= fb_base_addr;
                    end
                end

                FETCH_LINE: begin
                    if (m_arvalid && m_arready) begin
                        m_arvalid <= 1'b0;
                        m_rready  <= 1'b1;
                    end
                end

                WAIT_DATA: begin
                    if (m_rvalid && m_rready) begin
                        if (read_count == 8'd0) begin
                            m_rready <= 1'b0;
                        end else begin
                            read_count <= read_count - 8'd1;
                        end
                    end
                end
            endcase
        end
    end

    always_ff @(posedge pixel_clk or negedge rst_n) begin
        if (!rst_n) begin
            state_reg  <= IDLE;
            read_count <= 8'd0;
        end else begin
            state_reg  <= state_next;
            read_count <= read_count;
        end
    end

    always_comb begin
        state_next = state_reg;

        case (state_reg)
            IDLE: begin
                if (frame_start) begin
                    line_base_addr = fb_base_addr;
                    pixels_in_line = 8'd240; // 1920 pixels / 8 bytes per AXI beat
                    state_next     = FETCH_LINE;
                end
            end

            FETCH_LINE: begin
                if (m_arvalid && m_arready) begin
                    m_arlen     = 8'd15; // Burst of 16 beats
                    m_arsize    = 3'd3;  // 8 bytes per beat
                    m_arburst   = 2'd1;  // INCR
                    m_araddr    = line_base_addr;
                    read_count  = 8'd16; // 16 beats per line
                    state_next  = WAIT_DATA;
                end
            end

            WAIT_DATA: begin
                if (m_rvalid && m_rready && read_count == 8'd1) begin
                    state_next = PARSE_PIXEL;
                end
            end

            PARSE_PIXEL: begin
                if (buffer_valid) begin
                    state_next = DONE;
                end
            end

            DONE: begin
                state_next = IDLE;
            end

            default: state_next = IDLE;
        endcase
    end

    // -------------------------------------------------------------------------
    // Pixel Data FIFO
    // -------------------------------------------------------------------------
    fifo_sync #(
        .WIDTH              (FIFO_WIDTH),
        .DEPTH              (FIFO_DEPTH)
    ) pixel_fifo (
        .clk                (pixel_clk),
        .rst_n              (rst_n),
        .wr_en              (fifo_wr_en),
        .wr_data            (fifo_wr_data),
        .full               (fifo_full),
        .rd_en              (fifo_rd_en),
        .rd_data            (fifo_rd_data),
        .empty              (fifo_empty),
        .count              (fifo_count)
    );

    assign fifo_wr_en = m_rvalid && m_rready;
    assign fifo_wr_data = m_rdata;

    // -------------------------------------------------------------------------
    // Pixel Format Parser
    // -------------------------------------------------------------------------
    always_ff @(posedge pixel_clk or negedge rst_n) begin
        if (!rst_n) begin
            pixel_index  <= 3'd0;
            buffer_valid <= 1'b0;
        end else begin
            if (fifo_rd_en && !fifo_empty) begin
                pixel_index <= pixel_index + 3'd1;

                if (pixel_index == 3'd7) begin
                    buffer_valid <= 1'b1;
                end
            end else begin
                buffer_valid <= 1'b0;
            end
        end
    end

    always_comb begin
        fifo_rd_en = !fifo_empty && (state_reg == PARSE_PIXEL);

        case (pixel_format)
            FMT_RGB888: begin
                pixel_data_r = {fifo_rd_data[23:16], 24'd0};
                pixel_data_g = {fifo_rd_data[15:8], 24'd0};
                pixel_data_b = {fifo_rd_data[7:0], 24'd0};
            end

            FMT_RGB565: begin
                pixel_data_r = {fifo_rd_data[4:0], 24'd0};
                pixel_data_g = {fifo_rd_data[10:5], 24'd0};
                pixel_data_b = {fifo_rd_data[15:11], 24'd0};
            end

            FMT_RGBA8888: begin
                pixel_data_r = {fifo_rd_data[23:16], 24'd0};
                pixel_data_g = {fifo_rd_data[15:8], 24'd0};
                pixel_data_b = {fifo_rd_data[7:0], 24'd0};
            end

            FMT_YUV422: begin
                pixel_data_r = {fifo_rd_data[15:8], 24'd0};
                pixel_data_g = {fifo_rd_data[23:16], 24'd0};
                pixel_data_b = {fifo_rd_data[7:0], 24'd0};
            end

            default: begin
                pixel_data_r = 32'd0;
                pixel_data_g = 32'd0;
                pixel_data_b = 32'd0;
            end
        endcase
    end

    assign pixel_valid = buffer_valid;

endmodule
