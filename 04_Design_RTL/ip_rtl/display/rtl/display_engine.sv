// -----------------------------------------------------------------------------
// File: display_engine.sv
// Description: Display Engine - Timing Generator and Coordinate Manager
// Author: YaoGuang SoC Design Team
// Date: 2026-01-18
// -----------------------------------------------------------------------------

`timescale 1ns/1ps

module display_engine #(
    parameter integer NUM_CHANNELS = 3
) (
    input  logic                                    pixel_clk,
    input  logic                                    rst_n,
    input  logic                                    disp_enable,
    input  logic [1:0]                              output_sel,
    input  logic [31:0]                             fb_base_addr,
    input  logic [31:0]                             fb_stride,
    input  logic [7:0]                              pixel_format,

    output logic                                    frame_start,
    output logic                                    line_start,
    output logic                                    pixel_valid,
    output logic [31:0]                             pixel_data_r,
    output logic [31:0]                             pixel_data_g,
    output logic [31:0]                             pixel_data_b,
    output logic                                    pixel_de,
    output logic                                    pixel_hsync,
    output logic                                    pixel_vsync,

    // AXI Master Interface
    output logic [31:0]                             m_araddr,
    output logic [7:0]                             m_arlen,
    output logic [2:0]                             m_arsize,
    output logic [1:0]                             m_arburst,
    output logic                                    m_arvalid,
    input  logic                                    m_arready,
    input  logic [63:0]                             m_rdata,
    input  logic [1:0]                             m_rresp,
    input  logic                                    m_rvalid,
    output logic                                    m_rready
);

    // Timing Parameters (1920x1080@60Hz default)
    localparam integer H_TOTAL    = 2200;
    localparam integer H_ACTIVE   = 1920;
    localparam integer H_FP       = 88;
    localparam integer H_SYNC     = 44;
    localparam integer H_BP       = 148;
    localparam integer V_TOTAL    = 1125;
    localparam integer V_ACTIVE   = 1080;
    localparam integer V_FP       = 4;
    localparam integer V_SYNC     = 5;
    localparam integer V_BP       = 36;

    // FSM State Definition
    typedef enum logic [2:0] {
        IDLE      = 3'd0,
        INIT      = 3'd1,
        ACTIVE    = 3'd2,
        HSYNC     = 3'd3,
        HBP       = 3'd4,
        VSYNC     = 3'd5,
        VBP       = 3'd6,
        FRAME_END = 3'd7
    } state_t;

    // Registers
    state_t                                         state_reg, state_next;
    logic [11:0]                                    h_counter, h_counter_next;
    logic [11:0]                                    v_counter, v_counter_next;
    logic                                           hsync_reg, hsync_next;
    logic                                           vsync_reg, vsync_next;
    logic                                           de_reg, de_next;
    logic [31:0]                                    line_addr, line_addr_next;
    logic [11:0]                                    pixel_x, pixel_x_next;
    logic [11:0]                                    pixel_y, pixel_y_next;

    // AXI Control
    logic                                           axi_req;
    logic [31:0]                                    axi_addr;
    logic                                           axi_last;
    logic [1:0]                                     axi_resp;

    // -------------------------------------------------------------------------
    // Timing Generation FSM
    // -------------------------------------------------------------------------
    always_ff @(posedge pixel_clk or negedge rst_n) begin
        if (!rst_n) begin
            state_reg    <= IDLE;
            h_counter    <= 12'd0;
            v_counter    <= 12'd0;
            hsync_reg    <= 1'b0;
            vsync_reg    <= 1'b0;
            de_reg       <= 1'b0;
            line_addr    <= 32'd0;
            pixel_x      <= 12'd0;
            pixel_y      <= 12'd0;
        end else begin
            state_reg    <= state_next;
            h_counter    <= h_counter_next;
            v_counter    <= v_counter_next;
            hsync_reg    <= hsync_next;
            vsync_reg    <= vsync_next;
            de_reg       <= de_next;
            line_addr    <= line_addr_next;
            pixel_x      <= pixel_x_next;
            pixel_y      <= pixel_y_next;
        end
    end

    // -------------------------------------------------------------------------
    // FSM Next State Logic
    // -------------------------------------------------------------------------
    always_comb begin
        state_next     = state_reg;
        h_counter_next = h_counter;
        v_counter_next = v_counter;
        hsync_next     = hsync_reg;
        vsync_next     = vsync_reg;
        de_next        = de_reg;
        line_addr_next = line_addr;
        pixel_x_next   = pixel_x;
        pixel_y_next   = pixel_y;

        if (!disp_enable) begin
            state_next = IDLE;
            hsync_next = 1'b0;
            vsync_next = 1'b0;
            de_next    = 1'b0;
            return;
        end

        case (state_reg)
            IDLE: begin
                if (disp_enable) begin
                    state_next    = INIT;
                    h_counter_next = 12'd0;
                    v_counter_next = 12'd0;
                end
            end

            INIT: begin
                state_next    = ACTIVE;
                h_counter_next = 12'd0;
                v_counter_next = 12'd0;
                line_addr_next = fb_base_addr;
            end

            ACTIVE: begin
                h_counter_next = h_counter + 12'd1;

                if (h_counter >= H_ACTIVE - 12'd1) begin
                    de_next    = 1'b0;
                    hsync_next = 1'b1;
                    state_next = HSYNC;
                end else begin
                    de_next    = 1'b1;
                    pixel_x_next = h_counter;
                    pixel_y_next = v_counter;
                end
            end

            HSYNC: begin
                h_counter_next = h_counter + 12'd1;

                if (h_counter >= H_ACTIVE + H_FP - 12'd1) begin
                    hsync_next = 1'b0;
                    state_next = HBP;
                end
            end

            HBP: begin
                h_counter_next = h_counter + 12'd1;

                if (h_counter >= H_ACTIVE + H_FP + H_SYNC - 12'd1) begin
                    state_next = NEXT_LINE;
                end
            end

            NEXT_LINE: begin
                h_counter_next = 12'd0;
                v_counter_next = v_counter + 12'd1;
                line_addr_next = line_addr + fb_stride;

                if (v_counter >= V_ACTIVE - 12'd1) begin
                    vsync_next = 1'b1;
                    state_next = VSYNC;
                end else begin
                    state_next = ACTIVE;
                end
            end

            VSYNC: begin
                v_counter_next = v_counter + 12'd1;

                if (v_counter >= V_ACTIVE + V_FP - 12'd1) begin
                    vsync_next = 1'b0;
                    state_next = VBP;
                end
            end

            VBP: begin
                v_counter_next = v_counter + 12'd1;

                if (v_counter >= V_ACTIVE + V_FP + V_SYNC - 12'd1) begin
                    state_next = FRAME_END;
                end
            end

            FRAME_END: begin
                v_counter_next = v_counter + 12'd1;

                if (v_counter >= V_TOTAL - 12'd1) begin
                    state_next    = INIT;
                    h_counter_next = 12'd0;
                    v_counter_next = 12'd0;
                    line_addr_next = fb_base_addr;
                end
            end

            default: state_next = IDLE;
        endcase
    end

    // -------------------------------------------------------------------------
    // Output Signal Assignment
    // -------------------------------------------------------------------------
    assign frame_start    = (state_reg == INIT) && disp_enable;
    assign line_start     = (state_reg == ACTIVE) && (h_counter == 12'd0);
    assign pixel_de       = de_reg;
    assign pixel_hsync    = hsync_reg;
    assign pixel_vsync    = vsync_reg;

    // -------------------------------------------------------------------------
    // Framebuffer Reader Integration
    // -------------------------------------------------------------------------
    framebuffer_reader #(
        .AXI_DATA_WIDTH     (64),
        .AXI_ADDR_WIDTH     (32)
    ) fb_reader (
        .pixel_clk          (pixel_clk),
        .rst_n              (rst_n),
        .frame_start        (frame_start),
        .fb_base_addr       (fb_base_addr),
        .fb_stride          (fb_stride),
        .pixel_format       (pixel_format),
        .pixel_x            (pixel_x),
        .pixel_y            (pixel_y),
        .pixel_valid        (pixel_valid),
        .pixel_data_r       (pixel_data_r),
        .pixel_data_g       (pixel_data_g),
        .pixel_data_b       (pixel_data_b),
        .m_araddr           (m_araddr),
        .m_arlen            (m_arlen),
        .m_arsize           (m_arsize),
        .m_arburst          (m_arburst),
        .m_arvalid          (m_arvalid),
        .m_arready          (m_arready),
        .m_rdata            (m_rdata),
        .m_rresp            (m_rresp),
        .m_rvalid           (m_rvalid),
        .m_rready           (m_rready)
    );

endmodule
