// ============================================================================
// Module: l3_mshr
// Description: L3 Cache Miss Status Handling Register
// Version: 1.0
// ============================================================================

module l3_mshr #(
    parameter NUM_MSHR = 32,
    parameter INDEX_WIDTH = 12,
    parameter TAG_WIDTH = 22
) (
    input  logic                          clk,
    input  logic                          rst_n,

    // 分配请求
    input  logic                          alloc,
    input  logic [31:0]                   addr,
    output logic [NUM_MSHR-1:0]           avail,

    // 释放请求
    input  logic                          free,
    input  logic [9:0]                    free_id,

    // Hit检测
    output logic                          hit,
    output logic [9:0]                    hit_id
);

    localparam MSHR_ID_WIDTH = $clog2(NUM_MSHR);

    typedef struct packed {
        logic [31:0]          addr;
        logic                 valid;
        logic [7:0]           master_id;
        logic                 read;
    } mshr_entry_t;

    mshr_entry_t [NUM_MSHR-1:0] mshr;
    logic [NUM_MSHR-1:0]        addr_match;

    // 初始化
    integer i;
    initial begin
        for (i = 0; i < NUM_MSHR; i++) begin
            mshr[i].valid = 0;
        end
    end

    // Avail信号
    assign avail = ~mshr[*].valid;

    // 地址匹配检测
    genvar j;
    generate
        for (j = 0; j < NUM_MSHR; j++) begin : MATCH
            assign addr_match[j] = mshr[j].valid && (mshr[j].addr == addr);
        end
    endgenerate

    // Hit检测
    assign hit = |addr_match;
    assign hit_id = addr_match[0] ? 0 :
                    addr_match[1] ? 1 :
                    addr_match[2] ? 2 :
                    addr_match[3] ? 3 :
                    addr_match[4] ? 4 :
                    addr_match[5] ? 5 :
                    addr_match[6] ? 6 :
                    addr_match[7] ? 7 :
                    addr_match[8] ? 8 :
                    addr_match[9] ? 9 :
                    addr_match[10] ? 10 :
                    addr_match[11] ? 11 :
                    addr_match[12] ? 12 :
                    addr_match[13] ? 13 :
                    addr_match[14] ? 14 : 15;

    // 分配
    logic [MSHR_ID_WIDTH-1:0] alloc_id;

    find_first_set #(
        .WIDTH(NUM_MSHR)
    ) u_find_first (
        .data(~mshr[*].valid),
        .first_set(alloc_id),
        .any(~mshr[*].valid)
    );

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < NUM_MSHR; i++) begin
                mshr[i].valid <= 0;
            end
        end else begin
            if (alloc) begin
                mshr[alloc_id].valid <= 1;
                mshr[alloc_id].addr <= addr;
            end
            if (free) begin
                mshr[free_id].valid <= 0;
            end
        end
    end

endmodule

// Find First Set模块
module find_first_set #(
    parameter WIDTH = 32
) (
    input  logic [WIDTH-1:0]              data,
    output logic [$clog2(WIDTH)-1:0]      first_set,
    output logic                          any
);

    assign any = |data;
    integer i;
    always_comb begin
        first_set = 0;
        for (int i = 0; i < WIDTH; i++) begin
            if (data[i]) begin
                first_set = i;
                break;
            end
        end
    end

endmodule
