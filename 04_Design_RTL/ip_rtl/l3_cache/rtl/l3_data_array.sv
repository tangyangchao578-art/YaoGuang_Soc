// ============================================================================
// Module: l3_data_array
// Description: L3 Cache Data Array SRAM
// Version: 1.0
// ============================================================================

module l3_data_array #(
    parameter WAYS = 16,
    parameter INDEX_WIDTH = 12,
    parameter DATA_WIDTH = 512
) (
    input  logic                          clk,
    input  logic                          rst_n,

    // 读请求接口
    input  logic [WAYS-1:0]               read_req,
    input  logic [INDEX_WIDTH-1:0]        read_index[WAYS],
    input  logic [WAYS-1:0]               read_way,

    // 写请求接口
    input  logic                          write_en,
    input  logic [INDEX_WIDTH-1:0]        write_index,
    input  logic [WAYS-1:0]               write_way,
    input  logic [DATA_WIDTH-1:0]         write_data,
    input  logic [63:0]                   write_mask,

    // 读数据输出
    output logic [DATA_WIDTH-1:0]         read_data[WAYS]
);

    localparam SETS = 1 << INDEX_WIDTH;
    localparam WORDS_PER_LINE = DATA_WIDTH / 64;  // 512/64 = 8 words

    // Data SRAM: [SETS][WAYS][DATA_WIDTH]
    logic [SETS-1:0][WAYS-1:0][DATA_WIDTH-1:0] data_sram;

    // 读数据
    genvar i, j;
    generate
        for (i = 0; i < WAYS; i++) begin : READ_PATH
            always_ff @(posedge clk) begin
                if (read_req[i]) begin
                    read_data[i] <= data_sram[read_index[i]][i];
                end
            end
        end
    endgenerate

    // 写数据（字节级掩码）
    genvar way, word;
    generate
        for (way = 0; way < WAYS; way++) begin : WRITE_PATH
            always_ff @(posedge clk) begin
                if (write_en && write_way[way]) begin
                    for (int w = 0; w < WORDS_PER_LINE; w++) begin
                        if (write_mask[w]) begin
                            data_sram[write_index][way][w*64 +: 64] <= 
                                write_data[w*64 +: 64];
                        end
                    end
                end
            end
        end
    endgenerate

endmodule
