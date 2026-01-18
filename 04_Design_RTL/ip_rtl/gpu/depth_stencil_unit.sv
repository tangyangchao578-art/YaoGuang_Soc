//==============================================================================
//  Depth Stencil Unit - YaoGuang SoC
//==============================================================================
//  File: depth_stencil_unit.sv
//  Description: 深度/模板测试单元模块
//==============================================================================

`timescale 1ns/100ps

module depth_stencil_unit #(
    parameter int DATA_WIDTH = 256,
    parameter int Z_BUFFER_DEPTH = 24,
    parameter int STENCIL_DEPTH = 8,
    parameter int MAX_TILE_WIDTH = 32,
    parameter int MAX_TILE_HEIGHT = 32
) (
    //============= 时钟复位 =============
    input  logic                        clk_i,
    input  logic                        rst_n_i,
    input  logic                        enable_i,

    //============= 控制接口 =============
    output logic                        busy_o,

    //============= 深度测试配置 =============
    input  logic [31:0]                 depth_func_i,
    input  logic                        depth_test_enable_i,
    input  logic                        depth_write_enable_i,
    input  logic                        depth_clamp_enable_i,
    input  logic [Z_BUFFER_DEPTH-1:0]   depth_clear_value_i,

    //============= 模板测试配置 =============
    input  logic [31:0]                 stencil_func_i,
    input  logic [31:0]                 stencil_fail_op_i,
    input  logic [31:0]                 stencil_pass_depth_pass_op_i,
    input  logic [31:0]                 stencil_pass_depth_fail_op_i,
    input  logic [7:0]                  stencil_mask_i,
    input  logic [7:0]                  stencil_write_mask_i,
    input  logic [STENCIL_DEPTH-1:0]    stencil_clear_value_i,

    //============= 片元输入接口 =============
    input  logic [31:0]                 fragment_x_i,
    input  logic [31:0]                 fragment_y_i,
    input  logic [Z_BUFFER_DEPTH-1:0]   fragment_depth_i,
    input  logic [STENCIL_DEPTH-1:0]    fragment_stencil_i,
    input  logic                        fragment_valid_i,
    output logic                        fragment_ready_o,

    //============= 深度缓冲接口 =============
    output logic [31:0]                 zbuffer_addr_o,
    output logic                        zbuffer_read_o,
    input  logic [DATA_WIDTH-1:0]       zbuffer_rdata_i,
    output logic [DATA_WIDTH-1:0]       zbuffer_wdata_o,
    output logic                        zbuffer_write_o,
    input  logic                        zbuffer_ready_i,

    //============= 模板缓冲接口 =============
    output logic [31:0]                 stencil_addr_o,
    output logic                        stencil_read_o,
    input  logic [DATA_WIDTH-1:0]       stencil_rdata_i,
    output logic [DATA_WIDTH-1:0]       stencil_wdata_o,
    output logic                        stencil_write_o,
    input  logic                        stencil_ready_i,

    //============= 测试结果输出 =============
    output logic                        depth_test_pass_o,
    output logic                        stencil_test_pass_o,
    output logic                        all_test_pass_o,

    //============= 状态接口 =============
    output logic [31:0]                 test_pass_counter_o,
    output logic [31:0]                 test_fail_counter_o
);

    typedef enum logic [3:0] {
        IDLE,
        READ_ZBUFFER,
        READ_STENCIL,
        COMPARE_DEPTH,
        COMPARE_STENCIL,
        WRITE_BACK,
        DONE
    } state_t;

    state_t                              state_r, state_n;
    logic [31:0]                         test_pass_counter_r;
    logic [31:0]                         test_fail_counter_r;
    logic [Z_BUFFER_DEPTH-1:0]           zbuffer_value;
    logic [STENCIL_DEPTH-1:0]            stencil_value;
    logic                                current_depth_pass;
    logic                                current_stencil_pass;
    logic [3:0]                          zbuffer_byte_offset;
    logic [3:0]                          stencil_byte_offset;

    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            state_r <= IDLE;
            test_pass_counter_r <= '0;
            test_fail_counter_r <= '0;
        end else begin
            state_r <= state_n;
        end
    end

    always_comb begin
        state_n = state_r;
        fragment_ready_o = 1'b0;
        zbuffer_read_o = 1'b0;
        zbuffer_write_o = 1'b0;
        stencil_read_o = 1'b0;
        stencil_write_o = 1'b0;
        busy_o = 1'b1;

        case (state_r)
            IDLE: begin
                busy_o = 1'b0;
                fragment_ready_o = 1'b1;
                if (fragment_valid_i) begin
                    state_n = READ_ZBUFFER;
                end
            end

            READ_ZBUFFER: begin
                zbuffer_read_o = 1'b1;
                zbuffer_addr_o = {fragment_x_i[31:5], 5'b0};
                if (zbuffer_ready_i) begin
                    state_n = READ_STENCIL;
                end
            end

            READ_STENCIL: begin
                stencil_read_o = 1'b1;
                stencil_addr_o = {fragment_x_i[31:5], 5'b0};
                if (stencil_ready_i) begin
                    state_n = COMPARE_DEPTH;
                end
            end

            COMPARE_DEPTH: begin
                state_n = COMPARE_STENCIL;
            end

            COMPARE_STENCIL: begin
                if (all_test_pass_o) begin
                    state_n = WRITE_BACK;
                end else begin
                    state_n = DONE;
                end
            end

            WRITE_BACK: begin
                if (depth_write_enable_i) begin
                    zbuffer_write_o = 1'b1;
                    zbuffer_wdata_o = {208'h0, fragment_depth_i};
                end
                state_n = DONE;
            end

            DONE: begin
                if (all_test_pass_o) begin
                    test_pass_counter_r <= test_pass_counter_r + 1;
                end else begin
                    test_fail_counter_r <= test_fail_counter_r + 1;
                end
                state_n = IDLE;
            end

            default: state_n = IDLE;
        endcase
    end

    depth_comparator #(
        .DEPTH_WIDTH(Z_BUFFER_DEPTH)
    ) u_depth_comparator (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .enable_i(state_r == COMPARE_DEPTH),
        .depth_func_i(depth_func_i),
        .fragment_depth_i(fragment_depth_i),
        .zbuffer_value_i(zbuffer_value),
        .depth_test_enable_i(depth_test_enable_i),
        .depth_pass_o(current_depth_pass)
    );

    stencil_comparator #(
        .STENCIL_WIDTH(STENCIL_DEPTH)
    ) u_stencil_comparator (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .enable_i(state_r == COMPARE_STENCIL),
        .stencil_func_i(stencil_func_i),
        .fragment_stencil_i(fragment_stencil_i),
        .stencil_buffer_value_i(stencil_value),
        .stencil_mask_i(stencil_mask_i),
        .stencil_pass_o(current_stencil_pass)
    );

    assign zbuffer_byte_offset = fragment_x_i[4:0];
    assign stencil_byte_offset = fragment_x_i[4:0];

    always_ff @(posedge clk_i) begin
        if (zbuffer_read_o && zbuffer_ready_i) begin
            zbuffer_value <= zbuffer_rdata_i[zbuffer_byte_offset*8 +: Z_BUFFER_DEPTH];
        end
    end

    always_ff @(posedge clk_i) begin
        if (stencil_read_o && stencil_ready_i) begin
            stencil_value <= stencil_rdata_i[stencil_byte_offset*8 +: STENCIL_DEPTH];
        end
    end

    assign depth_test_pass_o = current_depth_pass;
    assign stencil_test_pass_o = current_stencil_pass;
    assign all_test_pass_o = depth_test_enable_i ? current_depth_pass : 1'b1;
    assign test_pass_counter_o = test_pass_counter_r;
    assign test_fail_counter_o = test_fail_counter_r;

endmodule
