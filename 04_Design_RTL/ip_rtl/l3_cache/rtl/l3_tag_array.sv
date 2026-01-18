// ============================================================================
// Module: l3_tag_array
// Description: L3 Cache Tag Array SRAM
// Version: 1.0
// ============================================================================

module l3_tag_array #(
    parameter WAYS = 16,
    parameter INDEX_WIDTH = 12,
    parameter TAG_WIDTH = 22
) (
    input  logic                          clk,
    input  logic                          rst_n,

    // 读请求接口
    input  logic [WAYS-1:0]               read_req,
    input  logic [INDEX_WIDTH-1:0]        read_index[WAYS],

    // 写请求接口
    input  logic [TAG_WIDTH-1:0]          write_addr,
    input  logic [INDEX_WIDTH-1:0]        write_index,
    input  logic [TAG_WIDTH-1:0]          write_data,
    input  logic                          write_en,
    input  logic [WAYS-1:0]               write_way,

    // 比较结果输出
    output logic [WAYS-1:0]               hit_way[WAYS],
    output logic [WAYS-1:0]               hit,
    output logic [WAYS-1:0]               dirty,
    output logic [WAYS-1:0]               valid,

    // 替换接口
    input  logic                          replace_valid,
    input  logic [INDEX_WIDTH-1:0]        replace_index,
    input  logic [WAYS-1:0]               replace_way,
    output logic                          replace_dirty,

    // 刷新接口
    input  logic                          cache_flush,
    output logic                          flush_done
);

    localparam SETS = 1 << INDEX_WIDTH;

    // Tag SRAM存储: [SETS][WAYS][TAG_WIDTH]
    logic [SETS-1:0][WAYS-1:0][TAG_WIDTH-1:0] tag_sram;
    logic [SETS-1:0][WAYS-1:0]                valid_sram;
    logic [SETS-1:0][WAYS-1:0]                dirty_sram;

    // Tag比较
    genvar i, j;
    generate
        for (i = 0; i < WAYS; i++) begin : READ_PATH
            // Tag SRAM读
            always_ff @(posedge clk) begin
                hit_way[i] <= 0;
                hit[i] <= 0;
                if (read_req[i]) begin
                    if (valid_sram[read_index[i]][i] &&
                        (tag_sram[read_index[i]][i] == write_addr)) begin
                        hit_way[i] <= 1'b1 << i;
                        hit[i] <= 1'b1;
                    end
                end
            end
        end
    endgenerate

    // 读dirty和valid
    generate
        for (i = 0; i < WAYS; i++) begin : STATUS_READ
            always_ff @(posedge clk) begin
                dirty[i] <= dirty_sram[read_index[0]][i];
                valid[i] <= valid_sram[read_index[0]][i];
            end
        end
    endgenerate

    // Tag SRAM写
    always_ff @(posedge clk) begin
        if (write_en) begin
            for (int i = 0; i < WAYS; i++) begin
                if (write_way[i]) begin
                    tag_sram[write_index][i] <= write_data;
                end
            end
        end
    end

    // Valid SRAM写
    always_ff @(posedge clk) begin
        if (write_en) begin
            for (int i = 0; i < WAYS; i++) begin
                if (write_way[i]) begin
                    valid_sram[write_index][i] <= 1'b1;
                end
            end
        end
    end

    // Dirty SRAM写
    always_ff @(posedge clk) begin
        if (write_en) begin
            for (int i = 0; i < WAYS; i++) begin
                if (write_way[i]) begin
                    dirty_sram[write_index][i] <= 1'b1;
                end
            end
        end
    end

    // 刷新逻辑
    logic [SETS-1:0] flush_counter;
    logic flush_in_progress;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            flush_in_progress <= 0;
            flush_counter <= 0;
            flush_done <= 0;
        end else begin
            if (cache_flush && !flush_in_progress) begin
                flush_in_progress <= 1;
                flush_counter <= 0;
                flush_done <= 0;
            end else if (flush_in_progress) begin
                if (flush_counter == SETS - 1) begin
                    flush_in_progress <= 0;
                    flush_done <= 1;
                end else begin
                    flush_counter <= flush_counter + 1;
                end
            end else begin
                flush_done <= 0;
            end
        end
    end

    // 清除valid和dirty
    integer k, m;
    always_ff @(posedge clk) begin
        if (flush_in_progress) begin
            for (m = 0; m < WAYS; m++) begin
                valid_sram[flush_counter][m] <= 0;
                dirty_sram[flush_counter][m] <= 0;
            end
        end
    end

    // 替换dirty输出
    assign replace_dirty = (replace_valid) ? dirty_sram[replace_index][replace_way] : 1'b0;

endmodule
