//==============================================================================
//  Vertex Processor - YaoGuang SoC
//==============================================================================
//  File: vertex_processor.sv
//  Description: 顶点处理器模块 - 负责顶点着色器执行
//==============================================================================

`timescale 1ns/100ps

module vertex_processor #(
    parameter int DATA_WIDTH = 256,
    parameter int VERTEX_ID_WIDTH = 16,
    parameter int UNIFORM_REG_COUNT = 64,
    parameter int ATTRIB_INDEX_WIDTH = 8,
    parameter int VARYING_COUNT = 16,
    parameter int MAX_VERTICES_PER_DRAW = 65536
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

    //============= 输入数据接口 =============
    input  logic [DATA_WIDTH-1:0]       input_vertex_data_i,
    input  logic                        input_valid_i,
    output logic                        input_ready_o,

    //============= 属性加载接口 =============
    output logic [31:0]                 attrib_base_addr_o,
    output logic [ATTRIB_INDEX_WIDTH-1:0] attrib_index_o,
    output logic                        attrib_fetch_o,
    input  logic [DATA_WIDTH-1:0]       attrib_data_i,
    input  logic                        attrib_valid_i,
    output logic                        attrib_ready_o,

    //============= Uniform 接口 =============
    output logic [31:0]                 uniform_addr_o,
    output logic                        uniform_fetch_o,
    input  logic [127:0]                uniform_data_i,
    input  logic                        uniform_valid_i,

    //============= 输出接口 =============
    output logic [DATA_WIDTH-1:0]       output_varying_o,
    output logic                        output_valid_o,
    input  logic                        output_ready_i,

    //============= 变换矩阵结果 =============
    output logic [127:0]                position_out_o,
    output logic                        position_valid_o,
    input  logic                        position_ready_i,

    //============= 状态接口 =============
    output logic [31:0]                 vertex_counter_o,
    output logic [31:0]                 perf_cycles_o
);

    typedef enum logic [3:0] {
        IDLE,
        FETCH_ATTRIB,
        FETCH_UNIFORM,
        EXECUTE_VS,
        OUTPUT_RESULT,
        DONE
    } state_t;

    state_t                              state_r, state_n;
    logic [31:0]                         vertex_counter_r;
    logic [31:0]                         cycle_counter_r;
    logic [31:0]                         uniform_reg [UNIFORM_REG_COUNT];
    logic [VARYING_COUNT-1:0][127:0]     varying_out;
    logic                                attrib_buffer_valid;

    logic [127:0]                        vertex_attrib [16];

    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            state_r <= IDLE;
            vertex_counter_r <= '0;
            cycle_counter_r <= '0;
            attrib_buffer_valid <= 1'b0;
        end else begin
            state_r <= state_n;
            if (enable_i) begin
                cycle_counter_r <= cycle_counter_r + 1;
                if (state_r == OUTPUT_RESULT && output_valid_o && output_ready_i) begin
                    vertex_counter_r <= vertex_counter_r + 1;
                end
            end
        end
    end

    always_comb begin
        state_n = state_r;
        input_ready_o = 1'b0;
        attrib_fetch_o = 1'b0;
        uniform_fetch_o = 1'b0;
        output_valid_o = 1'b0;
        position_valid_o = 1'b0;
        busy_o = 1'b1;
        done_o = 1'b0;

        case (state_r)
            IDLE: begin
                busy_o = 1'b0;
                if (start_i) begin
                    state_n = FETCH_ATTRIB;
                end
            end

            FETCH_ATTRIB: begin
                attrib_fetch_o = 1'b1;
                if (attrib_valid_i) begin
                    attrib_buffer_valid <= 1'b1;
                    state_n = FETCH_UNIFORM;
                end
            end

            FETCH_UNIFORM: begin
                uniform_fetch_o = 1'b1;
                if (uniform_valid_i) begin
                    state_n = EXECUTE_VS;
                end
            end

            EXECUTE_VS: begin
                state_n = OUTPUT_RESULT;
            end

            OUTPUT_RESULT: begin
                if (output_ready_i) begin
                    output_valid_o = 1'b1;
                    position_valid_o = 1'b1;
                    if (vertex_counter_r >= MAX_VERTICES_PER_DRAW - 1) begin
                        state_n = DONE;
                    end else begin
                        attrib_buffer_valid <= 1'b0;
                        state_n = FETCH_ATTRIB;
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

    vertex_shader_executor #(
        .DATA_WIDTH(DATA_WIDTH),
        .UNIFORM_COUNT(UNIFORM_REG_COUNT),
        .VARYING_COUNT(VARYING_COUNT)
    ) u_vs_executor (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .enable_i(state_r == EXECUTE_VS),
        .attrib_data_i(vertex_attrib),
        .attrib_valid_i(attrib_buffer_valid),
        .uniform_reg_i(uniform_reg),
        .position_o(position_out_o),
        .varying_o(varying_out),
        .output_valid_o(output_valid_o)
    );

    always_ff @(posedge clk_i) begin
        if (attrib_valid_i && attrib_ready_o) begin
            vertex_attrib[attrib_index_o] <= attrib_data_i[127:0];
        end
    end

    always_ff @(posedge clk_i) begin
        if (uniform_valid_i) begin
            uniform_reg[uniform_addr_o[7:0]] <= uniform_data_i[31:0];
        end
    end

    assign output_varying_o = varying_out[0];
    assign vertex_counter_o = vertex_counter_r;
    assign perf_cycles_o = cycle_counter_r;

endmodule
