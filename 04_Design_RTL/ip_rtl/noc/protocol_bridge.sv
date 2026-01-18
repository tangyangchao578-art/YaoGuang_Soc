`timescale 1ps/1ps

module protocol_bridge #
(
    parameter PROTOCOL_IN   = "AXI4",
    parameter PROTOCOL_OUT  = "NOC",
    parameter DATA_WIDTH    = 512,
    parameter ADDR_WIDTH    = 48,
    parameter ID_WIDTH      = 8,
    parameter USER_WIDTH    = 16,
    parameter VC_NUM        = 4,
    parameter CLK_PERIOD_PS = 500
)
(
    input  wire                         clk,
    input  wire                         rst_n,

    input  wire [ID_WIDTH-1:0]          mst_id,

    input  wire [DATA_WIDTH-1:0]        axi_aw_data,
    input  wire [ADDR_WIDTH-1:0]        axi_aw_addr,
    input  wire [ID_WIDTH-1:0]          axi_aw_id,
    input  wire [7:0]                   axi_aw_len,
    input  wire [2:0]                   axi_aw_size,
    input  wire [1:0]                   axi_aw_burst,
    input  wire                         axi_aw_valid,
    output wire                         axi_aw_ready,

    input  wire [DATA_WIDTH-1:0]        axi_w_data,
    input  wire [(DATA_WIDTH/8)-1:0]    axi_w_strb,
    input  wire                         axi_w_last,
    input  wire                         axi_w_valid,
    output wire                         axi_w_ready,

    output wire [ID_WIDTH-1:0]          axi_b_id,
    output wire [1:0]                   axi_b_resp,
    output wire                         axi_b_valid,
    input  wire                         axi_b_ready,

    input  wire [DATA_WIDTH-1:0]        axi_ar_data,
    input  wire [ADDR_WIDTH-1:0]        axi_ar_addr,
    input  wire [ID_WIDTH-1:0]          axi_ar_id,
    input  wire [7:0]                   axi_ar_len,
    input  wire [2:0]                   axi_ar_size,
    input  wire [1:0]                   axi_ar_burst,
    input  wire                         axi_ar_valid,
    output wire                         axi_ar_ready,

    output wire [DATA_WIDTH-1:0]        axi_r_data,
    output wire [ID_WIDTH-1:0]          axi_r_id,
    output wire                         axi_r_last,
    output wire [1:0]                   axi_r_resp,
    output wire                         axi_r_valid,
    input  wire                         axi_r_ready,

    output wire [VC_NUM-1:0]            noc_vc_id,
    output wire [DATA_WIDTH-1:0]        noc_data_out,
    output wire [ADDR_WIDTH-1:0]        noc_addr_out,
    output wire                         noc_valid_out,
    input  wire                         noc_ready_in,

    input  wire [DATA_WIDTH-1:0]        noc_data_in,
    input  wire [ADDR_WIDTH-1:0]        noc_addr_in,
    input  wire [VC_NUM-1:0]            noc_vc_id_in,
    input  wire                         noc_valid_in,
    output wire                         noc_ready_out
);

    typedef struct packed {
        logic [ADDR_WIDTH-1:0]     addr;
        logic [ID_WIDTH-1:0]       id;
        logic [7:0]                len;
        logic [2:0]                size;
        logic [1:0]                burst;
        logic [3:0]                qos;
        logic [USER_WIDTH-1:0]     user;
    } axi_aw_t;

    typedef struct packed {
        logic [DATA_WIDTH-1:0]     data;
        logic [(DATA_WIDTH/8)-1:0] strb;
        logic                      last;
        logic [USER_WIDTH-1:0]     user;
    } axi_w_t;

    typedef struct packed {
        logic [ID_WIDTH-1:0]       id;
        logic [1:0]                resp;
        logic                      valid;
    } axi_b_t;

    typedef struct packed {
        logic [ADDR_WIDTH-1:0]     addr;
        logic [ID_WIDTH-1:0]       id;
        logic [7:0]                len;
        logic [2:0]                size;
        logic [1:0]                burst;
        logic [3:0]                qos;
        logic [USER_WIDTH-1:0]     user;
    } axi_ar_t;

    typedef struct packed {
        logic [DATA_WIDTH-1:0]     data;
        logic [ID_WIDTH-1:0]       id;
        logic                      last;
        logic [1:0]                resp;
        logic [USER_WIDTH-1:0]     user;
    } axi_r_t;

    axi_aw_t                            aw_reg;
    axi_w_t                             w_reg;
    axi_ar_t                            ar_reg;

    reg                                 aw_valid_reg;
    reg                                 w_valid_reg;
    reg                                 ar_valid_reg;

    wire                                fifo_aw_full;
    wire                                fifo_w_full;
    wire                                fifo_ar_full;
    wire                                fifo_aw_empty;
    wire                                fifo_w_empty;
    wire                                fifo_ar_empty;

    reg  [1:0]                          state_write;
    reg  [1:0]                          state_read;

    wire [DATA_WIDTH-1:0]              noc_flit_data;
    wire                                noc_flit_valid;
    wire                                noc_flit_ready;

    localparam WRITE_STATE_IDLE   = 2'b00;
    localparam WRITE_STATE_ADDR   = 2'b01;
    localparam WRITE_STATE_DATA   = 2'b10;
    localparam WRITE_STATE_RESP   = 2'b11;

    localparam READ_STATE_IDLE    = 2'b00;
    localparam READ_STATE_ADDR    = 2'b01;
    localparam READ_STATE_DATA    = 2'b10;

    assign axi_aw_ready = ~fifo_aw_full;
    assign axi_w_ready  = ~fifo_w_full;
    assign axi_ar_ready = ~fifo_ar_full;

    generate
        if (PROTOCOL_IN == "AXI4" && PROTOCOL_OUT == "NOC") begin : AXI4_TO_NOC
            axi_to_noc_bridge #
            (
                .DATA_WIDTH (DATA_WIDTH),
                .ADDR_WIDTH (ADDR_WIDTH),
                .ID_WIDTH   (ID_WIDTH),
                .USER_WIDTH (USER_WIDTH),
                .VC_NUM     (VC_NUM)
            )
            bridge_inst
            (
                .clk          (clk),
                .rst_n        (rst_n),

                .axi_aw_data  (axi_aw_data),
                .axi_aw_addr  (axi_aw_addr),
                .axi_aw_id    (axi_aw_id),
                .axi_aw_len   (axi_aw_len),
                .axi_aw_size  (axi_aw_size),
                .axi_aw_burst (axi_aw_burst),
                .axi_aw_valid (axi_aw_valid),
                .axi_aw_ready (axi_aw_ready),

                .axi_w_data   (axi_w_data),
                .axi_w_strb   (axi_w_strb),
                .axi_w_last   (axi_w_last),
                .axi_w_valid  (axi_w_valid),
                .axi_w_ready  (axi_w_ready),

                .axi_b_id     (axi_b_id),
                .axi_b_resp   (axi_b_resp),
                .axi_b_valid  (axi_b_valid),
                .axi_b_ready  (axi_b_ready),

                .axi_ar_data  (axi_ar_data),
                .axi_ar_addr  (axi_ar_addr),
                .axi_ar_id    (axi_ar_id),
                .axi_ar_len   (axi_ar_len),
                .axi_ar_size  (axi_ar_size),
                .axi_ar_burst (axi_ar_burst),
                .axi_ar_valid (axi_ar_valid),
                .axi_ar_ready (axi_ar_ready),

                .axi_r_data   (axi_r_data),
                .axi_r_id     (axi_r_id),
                .axi_r_last   (axi_r_last),
                .axi_r_resp   (axi_r_resp),
                .axi_r_valid  (axi_r_valid),
                .axi_r_ready  (axi_r_ready),

                .noc_data_out (noc_data_out),
                .noc_addr_out (noc_addr_out),
                .noc_vc_id    (noc_vc_id),
                .noc_valid_out (noc_valid_out),
                .noc_ready_in (noc_ready_in),

                .noc_data_in  (noc_data_in),
                .noc_addr_in  (noc_addr_in),
                .noc_vc_id_in (noc_vc_id_in),
                .noc_valid_in (noc_valid_in),
                .noc_ready_out (noc_ready_out)
            );
        end else begin : PASSTHROUGH
            assign noc_data_out = axi_aw_data;
            assign noc_addr_out = axi_aw_addr;
            assign noc_vc_id = '0;
            assign noc_valid_out = axi_aw_valid;

            assign axi_r_data = noc_data_in;
            assign axi_r_id = noc_vc_id_in[ID_WIDTH-1:0];
            assign axi_r_last = 1'b1;
            assign axi_r_resp = 2'b00;
            assign axi_r_valid = noc_valid_in;
            assign noc_ready_out = axi_r_ready;
        end
    endgenerate

endmodule

module axi_to_noc_bridge #
(
    parameter DATA_WIDTH = 512,
    parameter ADDR_WIDTH = 48,
    parameter ID_WIDTH   = 8,
    parameter USER_WIDTH = 16,
    parameter VC_NUM     = 4
)
(
    input  wire                         clk,
    input  wire                         rst_n,

    input  wire [DATA_WIDTH-1:0]        axi_aw_data,
    input  wire [ADDR_WIDTH-1:0]        axi_aw_addr,
    input  wire [ID_WIDTH-1:0]          axi_aw_id,
    input  wire [7:0]                   axi_aw_len,
    input  wire [2:0]                   axi_aw_size,
    input  wire [1:0]                   axi_aw_burst,
    input  wire                         axi_aw_valid,
    output wire                         axi_aw_ready,

    input  wire [DATA_WIDTH-1:0]        axi_w_data,
    input  wire [(DATA_WIDTH/8)-1:0]    axi_w_strb,
    input  wire                         axi_w_last,
    input  wire                         axi_w_valid,
    output wire                         axi_w_ready,

    output wire [ID_WIDTH-1:0]          axi_b_id,
    output wire [1:0]                   axi_b_resp,
    output wire                         axi_b_valid,
    input  wire                         axi_b_ready,

    input  wire [DATA_WIDTH-1:0]        axi_ar_data,
    input  wire [ADDR_WIDTH-1:0]        axi_ar_addr,
    input  wire [ID_WIDTH-1:0]          axi_ar_id,
    input  wire [7:0]                   axi_ar_len,
    input  wire [2:0]                   axi_ar_size,
    input  wire [1:0]                   axi_ar_burst,
    input  wire                         axi_ar_valid,
    output wire                         axi_ar_ready,

    output wire [DATA_WIDTH-1:0]        axi_r_data,
    output wire [ID_WIDTH-1:0]          axi_r_id,
    output wire                         axi_r_last,
    output wire [1:0]                   axi_r_resp,
    output wire                         axi_r_valid,
    input  wire                         axi_r_ready,

    output wire [DATA_WIDTH-1:0]        noc_data_out,
    output wire [ADDR_WIDTH-1:0]        noc_addr_out,
    output wire [VC_NUM-1:0]            noc_vc_id,
    output wire                         noc_valid_out,
    input  wire                         noc_ready_in,

    input  wire [DATA_WIDTH-1:0]        noc_data_in,
    input  wire [ADDR_WIDTH-1:0]        noc_addr_in,
    input  wire [VC_NUM-1:0]            noc_vc_id_in,
    input  wire                         noc_valid_in,
    output wire                         noc_ready_out
);

    typedef struct packed {
        logic [ADDR_WIDTH-1:0]     addr;
        logic [ID_WIDTH-1:0]       id;
        logic [7:0]                len;
        logic [2:0]                size;
        logic [1:0]                burst;
        logic [3:0]                qos;
        logic [USER_WIDTH-1:0]     user;
    } axi_aw_t;

    typedef struct packed {
        logic [DATA_WIDTH-1:0]     data;
        logic [(DATA_WIDTH/8)-1:0] strb;
        logic                      last;
        logic [USER_WIDTH-1:0]     user;
    } axi_w_t;

    typedef struct packed {
        logic [ADDR_WIDTH-1:0]     addr;
        logic [ID_WIDTH-1:0]       id;
        logic [7:0]                len;
        logic [2:0]                size;
        logic [1:0]                burst;
        logic [3:0]                qos;
        logic [USER_WIDTH-1:0]     user;
    } axi_ar_t;

    axi_aw_t                            aw_fifo_in;
    axi_w_t                             w_fifo_in;
    axi_aw_t                            aw_fifo_out;
    axi_w_t                             w_fifo_out;
    axi_ar_t                            ar_fifo_in;
    axi_ar_t                            ar_fifo_out;

    wire                                aw_fifo_wr;
    wire                                aw_fifo_rd;
    wire                                aw_fifo_full;
    wire                                aw_fifo_empty;

    wire                                w_fifo_wr;
    wire                                w_fifo_rd;
    wire                                w_fifo_full;
    wire                                w_fifo_empty;

    wire                                ar_fifo_wr;
    wire                                ar_fifo_rd;
    wire                                ar_fifo_full;
    wire                                ar_fifo_empty;

    reg  [1:0]                          wr_state;
    reg  [1:0]                          rd_state;
    reg  [7:0]                          wr_beat_cnt;
    reg  [7:0]                          rd_beat_cnt;
    reg  [ID_WIDTH-1:0]                 wr_id_reg;
    reg  [ID_WIDTH-1:0]                 rd_id_reg;

    wire                                wr_start;
    wire                                rd_start;

    localparam WR_IDLE = 2'b00;
    localparam WR_ADDR = 2'b01;
    localparam WR_DATA = 2'b10;
    localparam WR_RESP = 2'b11;

    localparam RD_IDLE = 2'b00;
    localparam RD_ADDR = 2'b01;
    localparam RD_DATA = 2'b10;

    assign aw_fifo_in = '{addr: axi_aw_addr, id: axi_aw_id, len: axi_aw_len,
                          size: axi_aw_size, burst: axi_aw_burst, qos: 4'd0, user: '0};
    assign ar_fifo_in = '{addr: axi_ar_addr, id: axi_ar_id, len: axi_ar_len,
                          size: axi_ar_size, burst: axi_ar_burst, qos: 4'd0, user: '0};

    assign aw_fifo_wr = axi_aw_valid && ~aw_fifo_full;
    assign w_fifo_wr  = axi_w_valid && ~w_fifo_full;
    assign ar_fifo_wr = axi_ar_valid && ~ar_fifo_full;

    assign axi_aw_ready = ~aw_fifo_full;
    assign axi_w_ready  = ~w_fifo_full;
    assign axi_ar_ready = ~ar_fifo_full;

    assign wr_start = aw_fifo_wr;
    assign rd_start = ar_fifo_wr;

    fifo_sync #
    (
        .DEPTH      (8),
        .WIDTH      ($bits(axi_aw_t)),
        .PROTECTED  (1)
    )
    aw_fifo
    (
        .clk        (clk),
        .rst_n      (rst_n),
        .wr_en      (aw_fifo_wr),
        .wr_data    (aw_fifo_in),
        .full       (aw_fifo_full),
        .rd_en      (aw_fifo_rd),
        .rd_data    (aw_fifo_out),
        .empty      (aw_fifo_empty)
    );

    fifo_sync #
    (
        .DEPTH      (32),
        .WIDTH      ($bits(axi_w_t)),
        .PROTECTED  (1)
    )
    w_fifo
    (
        .clk        (clk),
        .rst_n      (rst_n),
        .wr_en      (w_fifo_wr),
        .wr_data    ('{data: axi_w_data, strb: axi_w_strb, last: axi_w_last, user: '0}),
        .full       (w_fifo_full),
        .rd_en      (w_fifo_rd),
        .rd_data    (w_fifo_out),
        .empty      (w_fifo_empty)
    );

    fifo_sync #
    (
        .DEPTH      (8),
        .WIDTH      ($bits(axi_ar_t)),
        .PROTECTED  (1)
    )
    ar_fifo
    (
        .clk        (clk),
        .rst_n      (rst_n),
        .wr_en      (ar_fifo_wr),
        .wr_data    (ar_fifo_in),
        .full       (ar_fifo_full),
        .rd_en      (ar_fifo_rd),
        .rd_data    (ar_fifo_out),
        .empty      (ar_fifo_empty)
    );

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_state <= WR_IDLE;
            wr_beat_cnt <= 8'd0;
            wr_id_reg <= {ID_WIDTH{1'b0}};
        end else begin
            case (wr_state)
                WR_IDLE: begin
                    if (wr_start && ~aw_fifo_empty) begin
                        wr_state <= WR_DATA;
                        wr_beat_cnt <= aw_fifo_out.len;
                        wr_id_reg <= aw_fifo_out.id;
                    end
                end
                WR_DATA: begin
                    if (w_fifo_rd && w_fifo_out.last) begin
                        wr_state <= WR_RESP;
                    end
                end
                WR_RESP: begin
                    if (axi_b_ready) begin
                        wr_state <= WR_IDLE;
                    end
                end
            endcase
        end
    end

    always @(*) begin
        aw_fifo_rd = 1'b0;
        w_fifo_rd  = 1'b0;
        noc_valid_out = 1'b0;
        noc_data_out  = '0;
        noc_addr_out  = '0;
        noc_vc_id = '0;

        if (wr_state == WR_DATA) begin
            if (noc_ready_in) begin
                noc_valid_out = 1'b1;
                noc_data_out  = w_fifo_out.data;
                noc_addr_out  = aw_fifo_out.addr;
                noc_vc_id     = aw_fifo_out.qos[VC_NUM-1:0];
                w_fifo_rd     = 1'b1;
            end
        end
    end

    assign axi_b_id   = wr_id_reg;
    assign axi_b_resp = 2'b00;
    assign axi_b_valid = (wr_state == WR_RESP);

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_state <= RD_IDLE;
            rd_beat_cnt <= 8'd0;
            rd_id_reg <= {ID_WIDTH{1'b0}};
        end else begin
            case (rd_state)
                RD_IDLE: begin
                    if (rd_start && ~ar_fifo_empty) begin
                        rd_state <= RD_DATA;
                        rd_beat_cnt <= ar_fifo_out.len;
                        rd_id_reg <= ar_fifo_out.id;
                    end
                end
                RD_DATA: begin
                    if (axi_r_ready && axi_r_last) begin
                        rd_state <= RD_IDLE;
                    end
                end
            endcase
        end
    end

    always @(*) begin
        ar_fifo_rd = 1'b0;
        noc_ready_out = 1'b0;

        if (rd_state == RD_DATA) begin
            if (noc_valid_in) begin
                noc_ready_out = 1'b1;
                ar_fifo_rd    = 1'b1;
            end
        end
    end

    assign axi_r_data  = noc_data_in;
    assign axi_r_id    = rd_id_reg;
    assign axi_r_last  = (rd_beat_cnt == 8'd0);
    assign axi_r_resp  = 2'b00;
    assign axi_r_valid = noc_valid_in;

endmodule

module noc_packetizer #
(
    parameter DATA_WIDTH  = 512,
    parameter ADDR_WIDTH  = 48,
    parameter HDR_WIDTH   = 64
)
(
    input  wire                         clk,
    input  wire                         rst_n,

    input  wire [DATA_WIDTH-1:0]        payload,
    input  wire [ADDR_WIDTH-1:0]        addr,
    input  wire [7:0]                   len,
    input  wire [3:0]                   qos,
    input  wire                         valid_in,
    output wire                         ready_out,

    output wire [DATA_WIDTH-1:0]        flit_out,
    output wire                         flit_valid_out,
    input  wire                         flit_ready_in
);

    reg  [7:0]                          beat_cnt;
    wire                                last_beat;

    assign ready_out = flit_ready_in;
    assign last_beat = (beat_cnt == len);
    assign flit_out = {HDR_WIDTH{1'b0}} | payload;
    assign flit_valid_out = valid_in && ready_out;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            beat_cnt <= 8'd0;
        end else begin
            if (valid_in && ready_out) begin
                if (last_beat) begin
                    beat_cnt <= 8'd0;
                end else begin
                    beat_cnt <= beat_cnt + 1'b1;
                end
            end
        end
    end

endmodule

module noc_depacketizer #
(
    parameter DATA_WIDTH  = 512,
    parameter ADDR_WIDTH  = 48,
    parameter HDR_WIDTH   = 64
)
(
    input  wire                         clk,
    input  wire                         rst_n,

    input  wire [DATA_WIDTH-1:0]        flit_in,
    input  wire                         flit_valid_in,
    output wire                         flit_ready_out,

    output wire [DATA_WIDTH-1:0]        payload,
    output wire [ADDR_WIDTH-1:0]        addr,
    output wire [7:0]                   len,
    output wire                         last_out,
    output wire                         valid_out,
    input  wire                         ready_in
);

    reg  [7:0]                          beat_cnt;
    wire                                first_flit;
    wire                                last_flit;

    assign first_flit = (beat_cnt == 8'd0);
    assign last_flit  = last_out;

    assign payload = flit_in;
    assign addr    = flit_in[ADDR_WIDTH-1:0];
    assign len     = flit_in[15:8];
    assign last_out = last_flit;
    assign valid_out = flit_valid_in && flit_ready_out;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            beat_cnt <= 8'd0;
        end else begin
            if (flit_valid_in && flit_ready_out) begin
                if (last_flit) begin
                    beat_cnt <= 8'd0;
                end else begin
                    beat_cnt <= beat_cnt + 1'b1;
                end
            end
        end
    end

    assign flit_ready_out = ready_in;

endmodule
