// ============================================================================
// Module: l3_request_handler
// Description: L3 Cache Request Handler
// Version: 1.0
// ============================================================================

module l3_request_handler #(
    parameter NUM_MASTERS = 16,
    parameter NUM_MSHR = 32,
    parameter INDEX_WIDTH = 12,
    parameter TAG_WIDTH = 22,
    parameter DATA_WIDTH = 512
) (
    input  logic                          clk,
    input  logic                          rst_n,

    // 从接口（连接Master）
    input  logic [NUM_MASTERS-1:0]       saxi_awvalid,
    output logic [NUM_MASTERS-1:0]       saxi_awready,
    input  logic [NUM_MASTERS-1:0][31:0] saxi_awaddr,
    input  logic [NUM_MASTERS-1:0][7:0]  saxi_awlen,
    input  logic [NUM_MASTERS-1:0][2:0]  saxi_awsize,
    input  logic [NUM_MASTERS-1:0][1:0]  saxi_awburst,
    input  logic [NUM_MASTERS-1:0][3:0]  saxi_awqos,

    input  logic [NUM_MASTERS-1:0]       saxi_wvalid,
    output logic [NUM_MASTERS-1:0]       saxi_wready,
    input  logic [NUM_MASTERS-1:0][DATA_WIDTH-1:0] saxi_wdata,
    input  logic [NUM_MASTERS-1:0][63:0] saxi_wstrb,
    input  logic [NUM_MASTERS-1:0]       saxi_wlast,

    output logic [NUM_MASTERS-1:0]       saxi_bvalid,
    input  logic [NUM_MASTERS-1:0]       saxi_bready,
    output logic [NUM_MASTERS-1:0][1:0]  saxi_bresp,

    input  logic [NUM_MASTERS-1:0]       saxi_arvalid,
    output logic [NUM_MASTERS-1:0]       saxi_arready,
    input  logic [NUM_MASTERS-1:0][31:0] saxi_araddr,
    input  logic [NUM_MASTERS-1:0][7:0]  saxi_arlen,
    input  logic [NUM_MASTERS-1:0][2:0]  saxi_arsize,
    input  logic [NUM_MASTERS-1:0][1:0]  saxi_arburst,
    input  logic [NUM_MASTERS-1:0][3:0]  saxi_arqos,

    output logic [NUM_MASTERS-1:0]       saxi_rvalid,
    input  logic [NUM_MASTERS-1:0]       saxi_rready,
    output logic [NUM_MASTERS-1:0][DATA_WIDTH-1:0] saxi_rdata,
    output logic [NUM_MASTERS-1:0][1:0]  saxi_rresp,
    output logic [NUM_MASTERS-1:0]       saxi_rlast,

    // Cache接口
    input  logic [NUM_MASTERS-1:0]       tag_hit,
    input  logic [NUM_MASTERS-1:0][WAYS-1:0] tag_hit_way,
    input  logic [NUM_MASTERS-1:0][WAYS-1:0] tag_dirty,
    input  logic [DATA_WIDTH-1:0]        data_read_data[NUM_MASTERS],

    output logic [NUM_MASTERS-1:0]       tag_read_req,
    output logic [NUM_MASTERS-1:0][INDEX_WIDTH-1:0] tag_read_index,
    output logic                          tag_write_en,
    output logic [TAG_WIDTH-1:0]         tag_write_addr,
    output logic [INDEX_WIDTH-1:0]       tag_write_index,
    output logic [TAG_WIDTH-1:0]         tag_write_data,
    output logic [WAYS-1:0]              tag_write_way,

    output logic [NUM_MASTERS-1:0]       data_read_req,
    output logic [NUM_MASTERS-1:0][INDEX_WIDTH-1:0] data_read_index,
    output logic [WAYS-1:0]              data_read_way,
    output logic                          data_write_en,
    output logic [INDEX_WIDTH-1:0]       data_write_index,
    output logic [WAYS-1:0]              data_write_way,
    output logic [DATA_WIDTH-1:0]        data_write_data,
    output logic [63:0]                  data_write_mask,

    // MSHR接口
    output logic                          mshr_alloc,
    input  logic                          mshr_free,
    output logic [31:0]                   mshr_addr,
    input  logic [NUM_MSHR-1:0]           mshr_avail,

    // 替换接口
    input  logic                          replace_valid,
    input  logic [INDEX_WIDTH-1:0]        replace_index,
    input  logic [WAYS-1:0]               replace_way,
    output logic                          replace_dirty,

    // 主接口（连接NoC/DDR）
    output logic                          maxi_awvalid,
    input  logic                          maxi_awready,
    output logic [31:0]                   maxi_awaddr,
    output logic [7:0]                    maxi_awlen,
    output logic [2:0]                    maxi_awsize,
    output logic [1:0]                    maxi_awburst,
    output logic [3:0]                    maxi_awqos,

    output logic                          maxi_wvalid,
    input  logic                          maxi_wready,
    output logic [DATA_WIDTH-1:0]         maxi_wdata,
    output logic [63:0]                   maxi_wstrb,
    output logic                          maxi_wlast,

    input  logic                          maxi_bvalid,
    output logic                          maxi_bready,
    input  logic [1:0]                    maxi_bresp,

    output logic                          maxi_arvalid,
    input  logic                          maxi_arready,
    output logic [31:0]                   maxi_araddr,
    output logic [7:0]                    maxi_arlen,
    output logic [2:0]                    maxi_arsize,
    output logic [1:0]                    maxi_arburst,
    output logic [3:0]                    maxi_arqos,

    input  logic                          maxi_rvalid,
    output logic                          maxi_rready,
    input  logic [DATA_WIDTH-1:0]         maxi_rdata,
    input  logic [1:0]                    maxi_rresp,
    input  logic                          maxi_rlast,

    // 统计
    output logic [31:0]                   hit_count,
    output logic [31:0]                   miss_count
);

    localparam NUM_WAYS = 16;

    typedef enum logic [2:0] {
        IDLE,
        READ_TAG,
        READ_DATA,
        WRITE_BACK,
        FETCH_MEM,
        COMPLETE
    } state_t;

    // 请求队列
    typedef struct packed {
        logic [31:0]              addr;
        logic [7:0]               len;
        logic [2:0]               size;
        logic                     read;
        logic [3:0]               master_id;
        logic                     valid;
    } request_t;

    request_t [31:0]                 request_fifo;
    logic [4:0]                      request_wr_ptr;
    logic [4:0]                      request_rd_ptr;
    logic                            request_full;
    logic                            request_empty;

    // 状态机
    state_t [15:0]                   master_state;
    state_t                          mem_state;
    logic [7:0]                      mem_burst_cnt;
    logic [31:0]                     mem_addr;

    // 读处理
    genvar m;
    generate
        for (m = 0; m < NUM_MASTERS; m++) begin : READ_MASTER
            // 读请求仲裁
            assign saxi_arready[m] = (master_state[m] == IDLE) && !request_full;
            assign tag_read_req[m] = (master_state[m] == IDLE) && saxi_arvalid[m];
            assign tag_read_index[m] = saxi_araddr[m][INDEX_WIDTH+6-1:6];
            assign data_read_index[m] = saxi_araddr[m][INDEX_WIDTH+6-1:6];
            assign data_read_way[m] = 1'b1 << m;  // 使用master ID选择way

            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    master_state[m] <= IDLE;
                    saxi_rvalid[m] <= 0;
                    saxi_rdata[m] <= 0;
                    saxi_rresp[m] <= 0;
                    saxi_rlast[m] <= 0;
                end else begin
                    case (master_state[m])
                        IDLE: begin
                            saxi_rvalid[m] <= 0;
                            if (saxi_arvalid[m] && saxi_arready[m]) begin
                                // 发起读请求
                                master_state[m] <= READ_TAG;
                                // 记录请求
                                if (!request_full) begin
                                    request_fifo[request_wr_ptr] <= '{
                                        addr: saxi_araddr[m],
                                        len: saxi_arlen[m],
                                        size: saxi_arsize[m],
                                        read: 1'b1,
                                        master_id: m,
                                        valid: 1'b1
                                    };
                                end
                            end
                        end
                        READ_TAG: begin
                            if (tag_hit[m]) begin
                                // 命中
                                hit_count <= hit_count + 1;
                                master_state[m] <= READ_DATA;
                                saxi_rresp[m] <= 2'b00;  // OKAY
                            end else begin
                                // 未命中，分配MSHR
                                if (mshr_avail != 0) begin
                                    mshr_alloc <= 1;
                                    mshr_addr <= saxi_araddr[m];
                                    master_state[m] <= FETCH_MEM;
                                    miss_count <= miss_count + 1;
                                end
                            end
                        end
                        READ_DATA: begin
                            // 发送数据
                            if (saxi_rready[m]) begin
                                saxi_rvalid[m] <= 1;
                                saxi_rdata[m] <= data_read_data[m];
                                saxi_rlast[m] <= 1;
                                if (saxi_rlast[m]) begin
                                    master_state[m] <= IDLE;
                                end
                            end
                        end
                        FETCH_MEM: begin
                            mshr_alloc <= 0;
                            // 等待内存数据
                            if (maxi_rvalid) begin
                                saxi_rvalid[m] <= 1;
                                saxi_rdata[m] <= maxi_rdata;
                                saxi_rlast[m] <= maxi_rlast;
                                if (maxi_rlast) begin
                                    master_state[m] <= IDLE;
                                end
                            end
                        end
                    endcase
                end
            end
        end
    endgenerate

    // 写处理
    genvar w;
    generate
        for (w = 0; w < NUM_MASTERS; w++) begin : WRITE_MASTER
            assign saxi_awready[w] = 1;  // 简化的写处理
            assign saxi_wready[w] = 1;
            assign saxi_bvalid[w] = 1;
            assign saxi_bresp[w] = 2'b00;
        end
    endgenerate

    // 内存访问控制器
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mem_state <= IDLE;
            maxi_arvalid <= 0;
            maxi_awvalid <= 0;
            maxi_rready <= 0;
            maxi_bready <= 0;
            mem_burst_cnt <= 0;
        end else begin
            case (mem_state)
                IDLE: begin
                    if (mshr_alloc) begin
                        // 发起内存读
                        maxi_arvalid <= 1;
                        maxi_araddr <= mshr_addr;
                        maxi_arlen <= 8'd15;  // 16-beat burst
                        maxi_arsize <= 3'd6;  // 64 bytes
                        maxi_arburst <= 2'b01;  // INCR
                        mem_state <= FETCH_MEM;
                        mem_addr <= mshr_addr;
                    end
                end
                FETCH_MEM: begin
                    if (maxi_arvalid && maxi_arready) begin
                        maxi_arvalid <= 0;
                    end
                    maxi_rready <= 1;
                    if (maxi_rvalid) begin
                        // 接收数据
                        mem_burst_cnt <= mem_burst_cnt + 1;
                        if (maxi_rlast) begin
                            maxi_rready <= 0;
                            mem_burst_cnt <= 0;
                            mshr_free <= 1;
                            mem_state <= IDLE;
                        end
                    end
                end
            endcase
        end
    endalways

    // 统计计数
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            hit_count <= 0;
            miss_count <= 0;
            mshr_alloc <= 0;
            mshr_free <= 0;
        end else begin
            mshr_alloc <= 0;
            mshr_free <= 0;
        end
    end

endmodule
