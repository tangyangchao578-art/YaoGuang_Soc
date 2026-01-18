//==============================================================================
//  Fragment Processor - YaoGuang SoC
//==============================================================================
//  File: fragment_processor.sv
//  Description: 片元处理器模块 - 负责片段着色器执行
//==============================================================================

`timescale 1ns/100ps

module fragment_processor #(
    parameter int DATA_WIDTH = 256,
    parameter int SAMPLER_COUNT = 16,
    parameter int UNIFORM_REG_COUNT = 256,
    parameter int VARYING_COUNT = 32,
    parameter int MAX_FRAGMENTS_PER_DRAW = 16777216
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

    //============= 输入接口 =============
    input  logic [127:0]                position_i,
    input  logic                        position_valid_i,
    output logic                        position_ready_o,
    input  logic [VARYING_COUNT-1:0][127:0] varying_i,
    input  logic                        varying_valid_i,
    output logic                        varying_ready_o,

    //============= 纹理采样接口 =============
    output logic [31:0]                 tex_coord_o [SAMPLER_COUNT],
    output logic [3:0]                  tex_sampler_o,
    output logic                        tex_fetch_o,
    input  logic [127:0]                tex_color_i,
    input  logic                        tex_valid_i,
    output logic                        tex_ready_o,

    //============= Uniform 接口 =============
    output logic [31:0]                 uniform_addr_o,
    output logic                        uniform_fetch_o,
    input  logic [127:0]                uniform_data_i,
    input  logic                        uniform_valid_i,

    //============= 输出接口 =============
    output logic [127:0]                color_out_o,
    output logic [3:0]                  color_channel_o,
    output logic                        color_valid_o,
    input  logic                        color_ready_i,

    //============= 深度/模板输出 =============
    output logic [31:0]                 depth_out_o,
    output logic                        depth_valid_o,
    input  logic                        depth_ready_i,

    //============= 状态接口 =============
    output logic [31:0]                 fragment_counter_o,
    output logic [31:0]                 perf_cycles_o
);

    typedef enum logic [3:0] {
        IDLE,
        FETCH_UNIFORM,
        FETCH_VARYING,
        FETCH_TEXTURE,
        EXECUTE_FS,
        OUTPUT_COLOR,
        DONE
    } state_t;

    state_t                              state_r, state_n;
    logic [31:0]                         fragment_counter_r;
    logic [31:0]                         cycle_counter_r;
    logic [31:0]                         uniform_reg [UNIFORM_REG_COUNT];
    logic [VARYING_COUNT-1:0][127:0]     varying_buffer;
    logic [127:0]                        tex_color_buffer;
    logic                                varying_buffer_valid;
    logic                                tex_buffer_valid;
    logic [3:0]                          current_sampler;

    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            state_r <= IDLE;
            fragment_counter_r <= '0;
            cycle_counter_r <= '0;
            varying_buffer_valid <= 1'b0;
            tex_buffer_valid <= 1'b0;
        end else begin
            state_r <= state_n;
            if (enable_i) begin
                cycle_counter_r <= cycle_counter_r + 1;
                if (state_r == OUTPUT_COLOR && color_valid_o && color_ready_i) begin
                    fragment_counter_r <= fragment_counter_r + 1;
                end
            end
        end
    end

    always_comb begin
        state_n = state_r;
        position_ready_o = 1'b0;
        varying_ready_o = 1'b0;
        tex_fetch_o = 1'b0;
        uniform_fetch_o = 1'b0;
        color_valid_o = 1'b0;
        depth_valid_o = 1'b0;
        busy_o = 1'b1;
        done_o = 1'b0;

        case (state_r)
            IDLE: begin
                busy_o = 1'b0;
                position_ready_o = 1'b1;
                if (position_valid_i) begin
                    varying_ready_o = 1'b1;
                    state_n = FETCH_VARYING;
                end
            end

            FETCH_VARYING: begin
                if (varying_valid_i) begin
                    varying_buffer_valid <= 1'b1;
                    state_n = FETCH_UNIFORM;
                end
            end

            FETCH_UNIFORM: begin
                uniform_fetch_o = 1'b1;
                if (uniform_valid_i) begin
                    state_n = FETCH_TEXTURE;
                end
            end

            FETCH_TEXTURE: begin
                tex_fetch_o = 1'b1;
                if (tex_valid_i) begin
                    tex_buffer_valid <= 1'b1;
                    state_n = EXECUTE_FS;
                end
            end

            EXECUTE_FS: begin
                state_n = OUTPUT_COLOR;
            end

            OUTPUT_COLOR: begin
                if (color_ready_i) begin
                    color_valid_o = 1'b1;
                    depth_valid_o = 1'b1;
                    if (fragment_counter_r >= MAX_FRAGMENTS_PER_DRAW - 1) begin
                        state_n = DONE;
                    end else begin
                        varying_buffer_valid <= 1'b0;
                        tex_buffer_valid <= 1'b0;
                        state_n = IDLE;
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

    fragment_shader_executor #(
        .DATA_WIDTH(DATA_WIDTH),
        .UNIFORM_COUNT(UNIFORM_REG_COUNT),
        .VARYING_COUNT(VARYING_COUNT),
        .SAMPLER_COUNT(SAMPLER_COUNT)
    ) u_fs_executor (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .enable_i(state_r == EXECUTE_FS),
        .varying_i(varying_buffer),
        .varying_valid_i(varying_buffer_valid),
        .uniform_reg_i(uniform_reg),
        .tex_color_i(tex_color_buffer),
        .tex_valid_i(tex_buffer_valid),
        .color_o(color_out_o),
        .color_channel_o(color_channel_o),
        .color_valid_o(color_valid_o),
        .depth_o(depth_out_o),
        .depth_valid_o(depth_valid_o)
    );

    always_ff @(posedge clk_i) begin
        if (varying_valid_i && varying_ready_o) begin
            varying_buffer <= varying_i;
        end
    end

    always_ff @(posedge clk_i) begin
        if (tex_valid_i && tex_ready_o) begin
            tex_color_buffer <= tex_color_i;
        end
    end

    always_ff @(posedge clk_i) begin
        if (uniform_valid_i) begin
            uniform_reg[uniform_addr_o[11:0]] <= uniform_data_i;
        end
    end

    assign fragment_counter_o = fragment_counter_r;
    assign perf_cycles_o = cycle_counter_r;

endmodule
