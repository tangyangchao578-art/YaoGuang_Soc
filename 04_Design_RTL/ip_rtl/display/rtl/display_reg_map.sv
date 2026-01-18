// -----------------------------------------------------------------------------
// File: display_reg_map.sv
// Description: Display Subsystem Register Map and APB Interface
// Author: YaoGuang SoC Design Team
// Date: 2026-01-18
// -----------------------------------------------------------------------------

`timescale 1ns/1ps

module display_reg_map #(
    parameter integer ADDR_WIDTH = 32
) (
    input  logic                                    clk,
    input  logic                                    rst_n,
    input  logic [ADDR_WIDTH-1:0]                  s_awaddr,
    input  logic                                    s_awvalid,
    output logic                                    s_awready,
    input  logic [31:0]                             s_wdata,
    input  logic [3:0]                              s_wstrb,
    input  logic                                    s_wvalid,
    output logic                                    s_wready,
    output logic [1:0]                             s_bresp,
    output logic                                    s_bvalid,
    input  logic                                    s_bready,
    input  logic [ADDR_WIDTH-1:0]                  s_araddr,
    input  logic                                    s_arvalid,
    output logic                                    s_arready,
    output logic [31:0]                            s_rdata,
    output logic [1:0]                             s_rresp,
    output logic                                    s_rvalid,
    input  logic                                    s_rready,

    output logic [31:0]                            reg_rdata,
    output logic                                    reg_ready,
    output logic                                    disp_enable,
    output logic [1:0]                             output_sel,
    output logic [ADDR_WIDTH-1:0]                  fb_base_addr,
    output logic [31:0]                            fb_stride,
    output logic [7:0]                             pixel_format,
    output logic                                    int_display
);

    // APB FSM
    typedef enum logic [1:0] {
        IDLE    = 2'd0,
        WDATA   = 2'd1,
        RDATA   = 2'd2
    } apb_state_t;

    apb_state_t                                     state_reg, state_next;
    logic [ADDR_WIDTH-1:0]                          addr_reg;

    // Register File
    logic [31:0]                                    reg_display_ctrl;
    logic [31:0]                                    reg_display_status;
    logic [31:0]                                    reg_timing_h_total;
    logic [31:0]                                    reg_timing_h_active;
    logic [31:0]                                    reg_timing_h_sync_start;
    logic [31:0]                                    reg_timing_h_sync_end;
    logic [31:0]                                    reg_timing_v_total;
    logic [31:0]                                    reg_timing_v_active;
    logic [31:0]                                    reg_timing_v_sync_start;
    logic [31:0]                                    reg_timing_v_sync_end;
    logic [31:0]                                    reg_fb_addr_l;
    logic [31:0]                                    reg_fb_addr_h;
    logic [31:0]                                    reg_fb_stride;
    logic [31:0]                                    reg_fb_format;
    logic [31:0]                                    reg_int_status;
    logic [31:0]                                    reg_int_mask;
    logic [31:0]                                    reg_color_space;
    logic [31:0]                                    reg_hdmi_ctrl;
    logic [31:0]                                    reg_dp_ctrl;
    logic [31:0]                                    reg_dsi_ctrl;

    // Interrupt Sources
    logic                                           int_frame_done;
    logic                                           int_vsync_edge;
    logic                                           int_fb_underrun;

    // -------------------------------------------------------------------------
    // APB Interface FSM
    // -------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state_reg <= IDLE;
            addr_reg <= '0;
        end else begin
            state_reg <= state_next;

            case (state_reg)
                IDLE: begin
                    if (s_awvalid || s_arvalid) begin
                        addr_reg <= s_awvalid ? s_awaddr : s_araddr;
                    end
                end

                default: ;
            endcase
        end
    end

    always_comb begin
        s_awready = (state_reg == IDLE) && s_awvalid;
        s_wready  = (state_reg == WDATA);
        s_arready = (state_reg == IDLE) && s_arvalid;
        s_rvalid  = (state_reg == RDATA);
        s_bvalid  = (state_reg == WDATA);

        state_next = state_reg;

        case (state_reg)
            IDLE: begin
                if (s_awvalid) begin
                    state_next = WDATA;
                end else if (s_arvalid) begin
                    state_next = RDATA;
                end
            end

            WDATA: begin
                if (s_wvalid && s_bready) begin
                    state_next = IDLE;
                end
            end

            RDATA: begin
                if (s_rready) begin
                    state_next = IDLE;
                end
            end
        endcase
    end

    assign s_bresp = 2'd0; // OKAY
    assign s_rresp = 2'd0; // OKAY

    // -------------------------------------------------------------------------
    // Register Write
    // -------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            reg_display_ctrl     <= 32'd0;
            reg_timing_h_total   <= 32'd2200;
            reg_timing_h_active  <= 32'd1920;
            reg_timing_h_sync_start <= 32'd2008;
            reg_timing_h_sync_end <= 32'd2052;
            reg_timing_v_total   <= 32'd1125;
            reg_timing_v_active  <= 32'd1080;
            reg_timing_v_sync_start <= 32'd1084;
            reg_timing_v_sync_end <= 32'd1089;
            reg_fb_addr_l        <= 32'd0;
            reg_fb_addr_h        <= 32'd0;
            reg_fb_stride        <= 32'd5760; // 1920 * 3 bytes
            reg_fb_format        <= 32'd0;
            reg_int_mask         <= 32'd0;
            reg_color_space      <= 32'd0;
            reg_hdmi_ctrl        <= 32'd0;
            reg_dp_ctrl          <= 32'd0;
            reg_dsi_ctrl         <= 32'd0;
        end else begin
            if (s_wvalid && s_wready) begin
                case (addr_reg[11:0])
                    12'h000: begin
                        if (s_wstrb[0]) reg_display_ctrl[7:0]   <= s_wdata[7:0];
                        if (s_wstrb[1]) reg_display_ctrl[15:8]  <= s_wdata[15:8];
                        if (s_wstrb[2]) reg_display_ctrl[23:16] <= s_wdata[23:16];
                        if (s_wstrb[3]) reg_display_ctrl[31:24] <= s_wdata[31:24];
                    end
                    12'h008: begin
                        if (s_wstrb[0]) reg_timing_h_total[7:0]   <= s_wdata[7:0];
                        if (s_wstrb[1]) reg_timing_h_total[15:8]  <= s_wdata[15:8];
                        if (s_wstrb[2]) reg_timing_h_total[23:16] <= s_wdata[23:16];
                        if (s_wstrb[3]) reg_timing_h_total[31:24] <= s_wdata[31:24];
                    end
                    12'h00C: begin
                        if (s_wstrb[0]) reg_timing_h_active[7:0]   <= s_wdata[7:0];
                        if (s_wstrb[1]) reg_timing_h_active[15:8]  <= s_wdata[15:8];
                        if (s_wstrb[2]) reg_timing_h_active[23:16] <= s_wdata[23:16];
                        if (s_wstrb[3]) reg_timing_h_active[31:24] <= s_wdata[31:24];
                    end
                    12'h018: begin
                        if (s_wstrb[0]) reg_timing_v_total[7:0]   <= s_wdata[7:0];
                        if (s_wstrb[1]) reg_timing_v_total[15:8]  <= s_wdata[15:8];
                        if (s_wstrb[2]) reg_timing_v_total[23:16] <= s_wdata[23:16];
                        if (s_wstrb[3]) reg_timing_v_total[31:24] <= s_wdata[31:24];
                    end
                    12'h01C: begin
                        if (s_wstrb[0]) reg_timing_v_active[7:0]   <= s_wdata[7:0];
                        if (s_wstrb[1]) reg_timing_v_active[15:8]  <= s_wdata[15:8];
                        if (s_wstrb[2]) reg_timing_v_active[23:16] <= s_wdata[23:16];
                        if (s_wstrb[3]) reg_timing_v_active[31:24] <= s_wdata[31:24];
                    end
                    12'h030: begin
                        if (s_wstrb[0]) reg_fb_addr_l[7:0]   <= s_wdata[7:0];
                        if (s_wstrb[1]) reg_fb_addr_l[15:8]  <= s_wdata[15:8];
                        if (s_wstrb[2]) reg_fb_addr_l[23:16] <= s_wdata[23:16];
                        if (s_wstrb[3]) reg_fb_addr_l[31:24] <= s_wdata[31:24];
                    end
                    12'h034: begin
                        if (s_wstrb[0]) reg_fb_addr_h[7:0]   <= s_wdata[7:0];
                        if (s_wstrb[1]) reg_fb_addr_h[15:8]  <= s_wdata[15:8];
                        if (s_wstrb[2]) reg_fb_addr_h[23:16] <= s_wdata[23:16];
                        if (s_wstrb[3]) reg_fb_addr_h[31:24] <= s_wdata[31:24];
                    end
                    12'h038: begin
                        if (s_wstrb[0]) reg_fb_stride[7:0]   <= s_wdata[7:0];
                        if (s_wstrb[1]) reg_fb_stride[15:8]  <= s_wdata[15:8];
                        if (s_wstrb[2]) reg_fb_stride[23:16] <= s_wdata[23:16];
                        if (s_wstrb[3]) reg_fb_stride[31:24] <= s_wdata[31:24];
                    end
                    12'h03C: begin
                        if (s_wstrb[0]) reg_fb_format[7:0]   <= s_wdata[7:0];
                        if (s_wstrb[1]) reg_fb_format[15:8]  <= s_wdata[15:8];
                        if (s_wstrb[2]) reg_fb_format[23:16] <= s_wdata[23:16];
                        if (s_wstrb[3]) reg_fb_format[31:24] <= s_wdata[31:24];
                    end
                    default: ;
                endcase
            end
        end
    end

    // -------------------------------------------------------------------------
    // Register Read
    // -------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            reg_rdata <= '0;
            reg_ready <= 1'b0;
        end else begin
            if (s_arvalid && s_arready) begin
                reg_ready <= 1'b1;
                case (addr_reg[11:0])
                    12'h000: reg_rdata <= reg_display_ctrl;
                    12'h004: reg_rdata <= reg_display_status;
                    12'h008: reg_rdata <= reg_timing_h_total;
                    12'h00C: reg_rdata <= reg_timing_h_active;
                    12'h010: reg_rdata <= reg_timing_h_sync_start;
                    12'h014: reg_rdata <= reg_timing_h_sync_end;
                    12'h018: reg_rdata <= reg_timing_v_total;
                    12'h01C: reg_rdata <= reg_timing_v_active;
                    12'h020: reg_rdata <= reg_timing_v_sync_start;
                    12'h024: reg_rdata <= reg_timing_v_sync_end;
                    12'h030: reg_rdata <= reg_fb_addr_l;
                    12'h034: reg_rdata <= reg_fb_addr_h;
                    12'h038: reg_rdata <= reg_fb_stride;
                    12'h03C: reg_rdata <= reg_fb_format;
                    12'h040: reg_rdata <= reg_int_status;
                    12'h044: reg_rdata <= reg_int_mask;
                    12'h100: reg_rdata <= reg_color_space;
                    12'h200: reg_rdata <= reg_hdmi_ctrl;
                    12'h300: reg_rdata <= reg_dp_ctrl;
                    12'h400: reg_rdata <= reg_dsi_ctrl;
                    default: reg_rdata <= '0;
                endcase
            end else begin
                reg_ready <= 1'b0;
            end
        end
    end

    // -------------------------------------------------------------------------
    // Register Output Assignment
    // -------------------------------------------------------------------------
    assign disp_enable   = reg_display_ctrl[0];
    assign output_sel    = reg_display_ctrl[5:4];
    assign fb_base_addr  = {reg_fb_addr_h[31:0], reg_fb_addr_l[31:0]};
    assign fb_stride     = reg_fb_stride;
    assign pixel_format  = reg_fb_format[3:0];

    // -------------------------------------------------------------------------
    // Interrupt Generation
    // -------------------------------------------------------------------------
    assign int_display = (reg_int_status[0] | reg_int_status[1] | reg_int_status[2]) &
                         ~reg_int_mask;

endmodule
