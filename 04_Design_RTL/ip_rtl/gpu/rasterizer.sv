//==============================================================================
//  Rasterizer - YaoGuang SoC
//==============================================================================
//  File: rasterizer.sv
//  Description: 光栅化单元模块
//==============================================================================

`timescale 1ns/100ps

module rasterizer #(
    parameter int MAX_TILE_WIDTH = 32,
    parameter int MAX_TILE_HEIGHT = 32,
    parameter int MAX_PRIMITIVES = 65536,
    parameter int VIEWPORT_WIDTH = 4096,
    parameter int VIEWPORT_HEIGHT = 4096,
    parameter int EDGE_FUNCTION_WIDTH = 32,
    parameter int VARYING_COUNT = 16
) (
    //============= 时钟复位 =============
    input  logic                        clk_i,
    input  logic                        rst_n_i,
    input  logic                        enable_i,

    //============= 控制接口 =============
    output logic                        busy_o,
    input  logic                        start_i,
    output logic                        done_o,
    input  logic [31:0]                 draw_id_i,

    //============= 顶点输入接口 =============
    input  logic [127:0]                v0_position_i,
    input  logic [127:0]                v1_position_i,
    input  logic [127:0]                v2_position_i,
    input  logic [VARYING_COUNT-1:0][127:0] v0_varying_i,
    input  logic [VARYING_COUNT-1:0][127:0] v1_varying_i,
    input  logic [VARYING_COUNT-1:0][127:0] v2_varying_i,
    input  logic                        primitive_valid_i,
    output logic                        primitive_ready_o,

    //============= 三角形属性 =============
    input  logic [31:0]                 cull_mode_i,
    input  logic [31:0]                 polygon_mode_i,
    input  logic [31:0]                 front_face_i,

    //============= 视口设置 =============
    input  logic [31:0]                 viewport_x_i,
    input  logic [31:0]                 viewport_y_i,
    input  logic [31:0]                 viewport_width_i,
    input  logic [31:0]                 viewport_height_i,

    //============= 片元输出接口 =============
    output logic [127:0]                fragment_position_o,
    output logic [VARYING_COUNT-1:0][127:0] fragment_varying_o,
    output logic                        fragment_valid_o,
    input  logic                        fragment_ready_i,

    //============= 状态接口 =============
    output logic [31:0]                 primitive_counter_o,
    output logic [31:0]                 fragment_counter_o,
    output logic [31:0]                 perf_cycles_o
);

    typedef enum logic [4:0] {
        IDLE,
        FETCH_PRIMITIVE,
        EDGE_FUNCTION,
        BINNING,
        RASTERIZE,
        INTERPOLATE,
        OUTPUT_FRAGMENT,
        DONE
    } state_t;

    state_t                              state_r, state_n;
    logic [31:0]                         primitive_counter_r;
    logic [31:0]                         fragment_counter_r;
    logic [31:0]                         cycle_counter_r;
    logic [31:0]                         tile_x, tile_y;
    logic [31:0]                         pixel_x, pixel_y;
    logic signed [EDGE_FUNCTION_WIDTH:0] edge0, edge1, edge2;
    logic signed [EDGE_FUNCTION_WIDTH:0] edge0_start, edge1_start, edge2_start;
    logic [VARYING_COUNT-1:0][127:0]     interpolated_varying;
    logic                                front_face;
    logic                                all_edges_negative;
    logic                                is_culled;

    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            state_r <= IDLE;
            primitive_counter_r <= '0;
            fragment_counter_r <= '0;
            cycle_counter_r <= '0;
        end else begin
            state_r <= state_n;
            if (enable_i) begin
                cycle_counter_r <= cycle_counter_r + 1;
                if (state_r == OUTPUT_FRAGMENT && fragment_valid_o && fragment_ready_i) begin
                    fragment_counter_r <= fragment_counter_r + 1;
                end
                if (state_r == FETCH_PRIMITIVE && primitive_valid_i) begin
                    primitive_counter_r <= primitive_counter_r + 1;
                end
            end
        end
    end

    always_comb begin
        state_n = state_r;
        primitive_ready_o = 1'b0;
        fragment_valid_o = 1'b0;
        busy_o = 1'b1;
        done_o = 1'b0;

        case (state_r)
            IDLE: begin
                busy_o = 1'b0;
                if (start_i) begin
                    state_n = FETCH_PRIMITIVE;
                end
            end

            FETCH_PRIMITIVE: begin
                primitive_ready_o = 1'b1;
                if (primitive_valid_i) begin
                    state_n = EDGE_FUNCTION;
                end
            end

            EDGE_FUNCTION: begin
                if (!is_culled) begin
                    state_n = RASTERIZE;
                end else begin
                    state_n = FETCH_PRIMITIVE;
                end
            end

            RASTERIZE: begin
                if (pixel_x < viewport_width_i && pixel_y < viewport_height_i) begin
                    if (all_edges_negative) begin
                        state_n = INTERPOLATE;
                    end else begin
                        pixel_x <= pixel_x + 1;
                        if (pixel_x >= viewport_width_i) begin
                            pixel_x <= 0;
                            pixel_y <= pixel_y + 1;
                        end
                    end
                end else begin
                    state_n = FETCH_PRIMITIVE;
                end
            end

            INTERPOLATE: begin
                state_n = OUTPUT_FRAGMENT;
            end

            OUTPUT_FRAGMENT: begin
                fragment_valid_o = 1'b1;
                if (fragment_ready_i) begin
                    fragment_counter_r <= fragment_counter_r + 1;
                    pixel_x <= pixel_x + 1;
                    if (pixel_x >= viewport_width_i) begin
                        pixel_x <= 0;
                        pixel_y <= pixel_y + 1;
                    end
                    if (pixel_y >= viewport_height_i) begin
                        state_n = FETCH_PRIMITIVE;
                    end else begin
                        state_n = RASTERIZE;
                    end
                end
            end

            DONE: begin
                done_o = 1'b1;
                state_n = IDLE;
            end

            default: state_n = IDLE;
        endcase
    end

    edge_function_calculator #(
        .EDGE_WIDTH(EDGE_FUNCTION_WIDTH)
    ) u_edge_calculator (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .enable_i(state_r == EDGE_FUNCTION),
        .v0_x_i(v0_position_i[31:0]),
        .v0_y_i(v0_position_i[63:32]),
        .v1_x_i(v1_position_i[31:0]),
        .v1_y_i(v1_position_i[63:32]),
        .v2_x_i(v2_position_i[31:0]),
        .v2_y_i(v2_position_i[63:32]),
        .pixel_x_i(pixel_x),
        .pixel_y_i(pixel_y),
        .edge0_o(edge0),
        .edge1_o(edge1),
        .edge2_o(edge2),
        .front_face_o(front_face),
        .all_negative_o(all_edges_negative),
        .is_culled_o(is_culled)
    );

    varying_interpolator #(
        .VARYING_COUNT(VARYING_COUNT),
        .FIXED_POINT_WIDTH(16)
    ) u_varying_interpolator (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .enable_i(state_r == INTERPOLATE),
        .v0_varying_i(v0_varying_i),
        .v1_varying_i(v1_varying_i),
        .v2_varying_i(v2_varying_i),
        .edge0_i(edge0),
        .edge1_i(edge1),
        .edge2_i(edge2),
        .pixel_x_i(pixel_x),
        .pixel_y_i(pixel_y),
        .interpolated_varying_o(interpolated_varying)
    );

    assign fragment_position_o = {96'h0, pixel_y[31:0], pixel_x[31:0]};
    assign fragment_varying_o = interpolated_varying;
    assign primitive_counter_o = primitive_counter_r;
    assign perf_cycles_o = cycle_counter_r;

endmodule
