//==============================================================================
//  Framebuffer Controller - YaoGuang SoC
//==============================================================================
//  File: framebuffer_controller.sv
//  Description: 帧缓冲控制模块
//==============================================================================

`timescale 1ns/100ps

module framebuffer_controller #(
    parameter int DATA_WIDTH = 256,
    parameter int MAX_FRAMEBUFFER_WIDTH = 4096,
    parameter int MAX_FRAMEBUFFER_HEIGHT = 4096,
    parameter int COLOR_BUFFER_DEPTH = 32,
    parameter int MAX_TILE_WIDTH = 32,
    parameter int MAX_TILE_HEIGHT = 32
) (
    //============= 时钟复位 =============
    input  logic                        clk_i,
    input  logic                        rst_n_i,
    input  logic                        enable_i,

    //============= 控制接口 =============
    output logic                        busy_o,

    //============= 帧缓冲配置 =============
    input  logic [31:0]                 framebuffer_base_addr_i,
    input  logic [15:0]                 framebuffer_width_i,
    input  logic [15:0]                 framebuffer_height_i,
    input  logic [4:0]                  color_format_i,
    input  logic                        scissor_test_enable_i,
    input  logic [31:0]                 scissor_x_i,
    input  logic [31:0]                 scissor_y_i,
    input  logic [31:0]                 scissor_width_i,
    input  logic [31:0]                 scissor_height_i,

    //============= 混合配置 =============
    input  logic                        blend_enable_i,
    input  logic [31:0]                 blend_func_rgb_i,
    input  logic [31:0]                 blend_func_alpha_i,
    input  logic [31:0]                 blend_equation_rgb_i,
    input  logic [31:0]                 blend_equation_alpha_i,
    input  logic [31:0]                 blend_src_rgb_i,
    input  logic [31:0]                 blend_dst_rgb_i,
    input  logic [31:0]                 blend_src_alpha_i,
    input  logic [31:0]                 blend_dst_alpha_i,

    //============= 颜色写入接口 =============
    input  logic [31:0]                 fragment_x_i,
    input  logic [31:0]                 fragment_y_i,
    input  logic [COLOR_BUFFER_DEPTH-1:0] fragment_color_i,
    input  logic                        color_valid_i,
    output logic                        color_ready_o,
    output logic                        color_discard_o,

    //============= L2 Cache 接口 =============
    output logic [31:0]                 cache_addr_o,
    output logic                        cache_read_o,
    input  logic [DATA_WIDTH-1:0]       cache_rdata_i,
    output logic [DATA_WIDTH-1:0]       cache_wdata_o,
    output logic                        cache_write_o,
    input  logic                        cache_ready_i,

    //============= 颜色缓冲接口 =============
    output logic [31:0]                 color_buffer_addr_o,
    output logic [DATA_WIDTH-1:0]       color_buffer_wdata_o,
    output logic                        color_buffer_write_o,
    input  logic                        color_buffer_ready_i,

    //============= 状态接口 =============
    output logic [31:0]                 pixel_counter_o,
    output logic [31:0]                 blend_counter_o
);

    typedef enum logic [4:0] {
        IDLE,
        READ_COLOR_BUFFER,
        BLEND,
        WRITE_COLOR_BUFFER,
        DONE
    } state_t;

    state_t                              state_r, state_n;
    logic [31:0]                         pixel_counter_r;
    logic [31:0]                         blend_counter_r;
    logic [COLOR_BUFFER_DEPTH-1:0]       current_color;
    logic [COLOR_BUFFER_DEPTH-1:0]       blended_color;
    logic                                is_outside_scissor;
    logic [4:0]                          byte_offset;

    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            state_r <= IDLE;
            pixel_counter_r <= '0;
            blend_counter_r <= '0;
        end else begin
            state_r <= state_n;
        end
    end

    always_comb begin
        state_n = state_r;
        color_ready_o = 1'b0;
        cache_read_o = 1'b0;
        cache_write_o = 1'b0;
        color_buffer_write_o = 1'b0;
        color_discard_o = 1'b0;
        busy_o = 1'b1;

        case (state_r)
            IDLE: begin
                busy_o = 1'b0;
                color_ready_o = 1'b1;
                if (color_valid_i) begin
                    if (is_outside_scissor) begin
                        color_discard_o = 1'b1;
                        state_n = DONE;
                    end else begin
                        state_n = READ_COLOR_BUFFER;
                    end
                end
            end

            READ_COLOR_BUFFER: begin
                cache_read_o = 1'b1;
                cache_addr_o = {framebuffer_base_addr_i[31:5], fragment_x_i[4:0], 5'b0};
                if (cache_ready_i) begin
                    state_n = BLEND;
                end
            end

            BLEND: begin
                if (blend_enable_i) begin
                    blend_counter_r <= blend_counter_r + 1;
                end
                state_n = WRITE_COLOR_BUFFER;
            end

            WRITE_COLOR_BUFFER: begin
                color_buffer_write_o = 1'b1;
                color_buffer_addr_o = {framebuffer_base_addr_i[31:5], fragment_x_i[4:0], 5'b0};
                color_buffer_wdata_o = {224'h0, blended_color};
                if (color_buffer_ready_i) begin
                    state_n = DONE;
                end
            end

            DONE: begin
                pixel_counter_r <= pixel_counter_r + 1;
                state_n = IDLE;
            end

            default: state_n = IDLE;
        endcase
    end

    color_blender #(
        .COLOR_DEPTH(COLOR_BUFFER_DEPTH)
    ) u_color_blender (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .enable_i(state_r == BLEND),
        .src_color_i(fragment_color_i),
        .dst_color_i(current_color),
        .blend_enable_i(blend_enable_i),
        .blend_func_rgb_i(blend_func_rgb_i),
        .blend_func_alpha_i(blend_func_alpha_i),
        .blend_equation_rgb_i(blend_equation_rgb_i),
        .blend_equation_alpha_i(blend_equation_alpha_i),
        .blended_color_o(blended_color)
    );

    always_ff @(posedge clk_i) begin
        if (cache_read_o && cache_ready_i) begin
            current_color <= cache_rdata_i[byte_offset*8 +: COLOR_BUFFER_DEPTH];
        end
    end

    assign byte_offset = fragment_x_i[4:0];

    always_comb begin
        is_outside_scissor = 1'b0;
        if (scissor_test_enable_i) begin
            if (fragment_x_i < scissor_x_i || fragment_x_i >= scissor_x_i + scissor_width_i ||
                fragment_y_i < scissor_y_i || fragment_y_i >= scissor_y_i + scissor_height_i) begin
                is_outside_scissor = 1'b1;
            end
        end
    end

    assign pixel_counter_o = pixel_counter_r;
    assign blend_counter_o = blend_counter_r;

endmodule
