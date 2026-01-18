// ============================================================================
// Module: l3_plru
// Description: L3 Cache Pseudo-LRU Replacement Policy
// Version: 1.0
// ============================================================================

module l3_plru #(
    parameter WAYS = 16
) (
    input  logic                          clk,
    input  logic                          rst_n,

    input  logic [11:0]                   index,
    input  logic [WAYS-1:0]               hit_way,
    input  logic [WAYS-1:0]               hit_valid,
    output logic [WAYS-1:0]               replace_way
);

    // PLRU树结构: 16-way需要15个位
    //        b0
    //     /     \
    //    b1      b2
    //   / \     / \
    //  b3 b4   b5 b6
    //  |  |   |  |
    //  w0 w1  w2 w3  ... etc

    localparam NUM_BITS = WAYS - 1;
    localparam NUM_LEAVES = WAYS;

    logic [NUM_BITS-1:0]                  plru_bits;
    logic [NUM_BITS-1:0]                 plru_bits_next;

    // PLRU位索引映射
    // Level 0: bit 0 (root)
    // Level 1: bits 1-2
    // Level 2: bits 3-6
    // Level 3: bits 7-14 (leaves)

    function [NUM_BITS-1:0] get_plru_update;
        input [WAYS-1:0]                 hit_way_local;
        integer i;
        begin
            get_plru_update = 0;
            // 根据命中的way更新PLRU位
            case (1)
                hit_way_local[0]: begin get_plru_update[0] = 0; get_plru_update[1] = 0; get_plru_update[3] = 0; end
                hit_way_local[1]: begin get_plru_update[0] = 0; get_plru_update[1] = 0; get_plru_update[3] = 1; end
                hit_way_local[2]: begin get_plru_update[0] = 0; get_plru_update[1] = 1; get_plru_update[5] = 0; end
                hit_way_local[3]: begin get_plru_update[0] = 0; get_plru_update[1] = 1; get_plru_update[5] = 1; end
                hit_way_local[4]: begin get_plru_update[0] = 1; get_plru_update[2] = 0; get_plru_update[7] = 0; end
                hit_way_local[5]: begin get_plru_update[0] = 1; get_plru_update[2] = 0; get_plru_update[7] = 1; end
                hit_way_local[6]: begin get_plru_update[0] = 1; get_plru_update[2] = 1; get_plru_update[9] = 0; end
                hit_way_local[7]: begin get_plru_update[0] = 1; get_plru_update[2] = 1; get_plru_update[9] = 1; end
                hit_way_local[8]: begin get_plru_update[0] = 0; get_plru_update[1] = 0; get_plru_update[3] = 0; end
                hit_way_local[9]: begin get_plru_update[0] = 0; get_plru_update[1] = 0; get_plru_update[3] = 1; end
                hit_way_local[10]: begin get_plru_update[0] = 0; get_plru_update[1] = 1; get_plru_update[5] = 0; end
                hit_way_local[11]: begin get_plru_update[0] = 0; get_plru_update[1] = 1; get_plru_update[5] = 1; end
                hit_way_local[12]: begin get_plru_update[0] = 1; get_plru_update[2] = 0; get_plru_update[7] = 0; end
                hit_way_local[13]: begin get_plru_update[0] = 1; get_plru_update[2] = 0; get_plru_update[7] = 1; end
                hit_way_local[14]: begin get_plru_update[0] = 1; get_plru_update[2] = 1; get_plru_update[9] = 0; end
                hit_way_local[15]: begin get_plru_update[0] = 1; get_plru_update[2] = 1; get_plru_update[9] = 1; end
            endcase
        end
    endfunction

    function [WAYS-1:0] get_replace_way;
        input [NUM_BITS-1:0]             bits;
        integer i;
        begin
            get_replace_way = 0;
            // 根据PLRU位选择替换的way
            if (!bits[0]) begin
                if (!bits[1]) begin
                    if (!bits[3]) get_replace_way[0] = 1;
                    else get_replace_way[1] = 1;
                end else begin
                    if (!bits[5]) get_replace_way[2] = 1;
                    else get_replace_way[3] = 1;
                end
            end else begin
                if (!bits[2]) begin
                    if (!bits[7]) get_replace_way[4] = 1;
                    else get_replace_way[5] = 1;
                end else begin
                    if (!bits[9]) get_replace_way[6] = 1;
                    else get_replace_way[7] = 1;
                end
            end
        end
    endfunction

    // PLRU SRAM
    logic [4095:0][NUM_BITS-1:0]          plru_sram;  // Per-set PLRU

    // 读PLRU位
    always_ff @(posedge clk) begin
        plru_bits <= plru_sram[index];
    end

    // 计算替换way
    assign replace_way = get_replace_way(plru_bits);

    // 更新PLRU位（命中时）
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            plru_sram <= 0;
        end else if (|hit_valid) begin
            plru_sram[index] <= get_plru_update(hit_way);
        end
    end

endmodule
