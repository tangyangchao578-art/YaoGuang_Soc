//==============================================================================
//  Texture Mapping Unit - YaoGuang SoC
//==============================================================================
//  File: texture_mapping_unit.sv
//  Description: 纹理映射单元模块
//==============================================================================

`timescale 1ns/100ps

module texture_mapping_unit #(
    parameter int TEX_WIDTH = 256,
    parameter int MAX_TEXTURE_SIZE = 16384,
    parameter int MAX_MIP_LEVELS = 14,
    parameter int SAMPLER_COUNT = 16,
    parameter int L1_CACHE_SIZE = 65536,
    parameter int CACHE_LINE_SIZE = 64
) (
    //============= 时钟复位 =============
    input  logic                        clk_i,
    input  logic                        rst_n_i,
    input  logic                        enable_i,

    //============= 控制接口 =============
    output logic                        busy_o,

    //============= 请求接口 =============
    input  logic [31:0]                 tex_coord_i [SAMPLER_COUNT],
    input  logic [3:0]                  sampler_index_i,
    input  logic                        request_valid_i,
    output logic                        request_ready_o,

    //============= 纹理数据接口 =============
    input  logic [31:0]                 texture_base_addr_i,
    input  logic [15:0]                 texture_width_i,
    input  logic [15:0]                 texture_height_i,
    input  logic [3:0]                  texture_format_i,
    input  logic [3:0]                  mip_level_i,
    input  logic                        texture_valid_i,
    output logic                        texture_ready_o,

    //============= 输出接口 =============
    output logic [127:0]                texel_color_o,
    output logic                        texel_valid_o,
    input  logic                        texel_ready_i,

    //============= L2 Cache 接口 =============
    output logic [31:0]                 cache_addr_o,
    output logic [TEX_WIDTH-1:0]        cache_wdata_o,
    input  logic [TEX_WIDTH-1:0]        cache_rdata_i,
    output logic                        cache_read_o,
    output logic                        cache_write_o,
    input  logic                        cache_ready_i,

    //============= 状态接口 =============
    output logic [31:0]                 texel_counter_o,
    output logic [31:0]                 cache_miss_o
);

    typedef enum logic [4:0] {
        IDLE,
        FETCH_TEX_DESC,
        CALC_ADDRESS,
        FETCH_TEXELS,
        FILTER,
        OUTPUT_RESULT,
        DONE
    } state_t;

    state_t                              state_r, state_n;
    logic [31:0]                         texel_counter_r;
    logic [31:0]                         cache_miss_r;
    logic [31:0]                         current_mip_size;
    logic [31:0]                         current_address;
    logic [15:0]                         u_coord, v_coord;
    logic [3:0]                          current_sampler;
    logic [127:0]                        texel_data [4];
    logic [1:0]                          texel_count;
    logic                                filtering_done;

    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            state_r <= IDLE;
            texel_counter_r <= '0;
            cache_miss_r <= '0;
        end else begin
            state_r <= state_n;
            if (enable_i && texel_valid_o && texel_ready_i) begin
                texel_counter_r <= texel_counter_r + 1;
            end
        end
    end

    always_comb begin
        state_n = state_r;
        request_ready_o = 1'b0;
        texture_ready_o = 1'b0;
        cache_read_o = 1'b0;
        cache_write_o = 1'b0;
        texel_valid_o = 1'b0;
        busy_o = 1'b1;

        case (state_r)
            IDLE: begin
                busy_o = 1'b0;
                request_ready_o = 1'b1;
                if (request_valid_i) begin
                    texture_ready_o = 1'b1;
                    state_n = FETCH_TEX_DESC;
                end
            end

            FETCH_TEX_DESC: begin
                if (texture_valid_i) begin
                    state_n = CALC_ADDRESS;
                end
            end

            CALC_ADDRESS: begin
                cache_read_o = 1'b1;
                cache_addr_o = current_address;
                if (cache_ready_i) begin
                    state_n = FETCH_TEXELS;
                end
            end

            FETCH_TEXELS: begin
                if (texel_count < 3) begin
                    cache_read_o = 1'b1;
                    cache_addr_o = current_address + (texel_count * 16);
                end else begin
                    state_n = FILTER;
                end
            end

            FILTER: begin
                if (filtering_done) begin
                    state_n = OUTPUT_RESULT;
                end
            end

            OUTPUT_RESULT: begin
                texel_valid_o = 1'b1;
                if (texel_ready_i) begin
                    state_n = IDLE;
                end
            end

            default: state_n = IDLE;
        endcase
    end

    texel_address_calculator #(
        .MAX_TEXTURE_SIZE(MAX_TEXTURE_SIZE),
        .MAX_MIP_LEVELS(MAX_MIP_LEVELS)
    ) u_addr_calculator (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .enable_i(state_r == CALC_ADDRESS),
        .u_coord_i(u_coord),
        .v_coord_i(v_coord),
        .texture_width_i(texture_width_i),
        .mip_level_i(mip_level_i),
        .texture_base_addr_i(texture_base_addr_i),
        .address_o(current_address),
        .mip_size_o(current_mip_size)
    );

    texture_filter #(
        .TEXEL_WIDTH(32)
    ) u_texture_filter (
        .clk_i(clk_i),
        .rst_n_i(rst_n_i),
        .enable_i(state_r == FILTER),
        .texel_data_i(texel_data),
        .filter_type_i(sampler_index_i[1:0]),
        .anisotropy_ratio_i(sampler_index_i[3:2]),
        .filtered_texel_o(texel_color_o),
        .done_o(filtering_done)
    );

    always_ff @(posedge clk_i) begin
        if (cache_ready_i && cache_read_o) begin
            texel_data[texel_count] <= cache_rdata_i[127:0];
            texel_count <= texel_count + 1;
        end
    end

    assign texel_counter_o = texel_counter_r;
    assign cache_miss_o = cache_miss_r;

endmodule
