`timescale 1ps/1ps

module virtual_channel #
(
    parameter VC_NUM        = 4,
    parameter VC_DEPTH      = 16,
    parameter DATA_WIDTH    = 512,
    parameter PRIO_WIDTH    = 2,
    parameter PKT_ID_WIDTH  = 8
)
(
    input  wire                         clk,
    input  wire                         rst_n,

    input  wire                         valid_in,
    input  wire [DATA_WIDTH-1:0]        data_in,
    input  wire [VC_NUM-1:0]            vc_id_in,
    input  wire [PRIO_WIDTH-1:0]        prio_in,
    input  wire [PKT_ID_WIDTH-1:0]      pkt_id_in,

    output wire                         flit_out,
    output wire [DATA_WIDTH+VC_NUM+PRIO_WIDTH+PKT_ID_WIDTH-1:0] flit_data,
    input  wire                         ready_in,

    input  wire [VC_NUM-1:0]            credit_in,
    output wire [VC_NUM-1:0]            credit_out,

    output wire [7:0]                   vc_status
);

    localparam LOG2_VC    = $clog2(VC_NUM);
    localparam LOG2_DEPTH = $clog2(VC_DEPTH);

    typedef struct packed {
        logic [DATA_WIDTH-1:0]     data;
        logic [PKT_ID_WIDTH-1:0]   pkt_id;
        logic [PRIO_WIDTH-1:0]     prio;
        logic [VC_NUM-1:0]         vc_id;
    } flit_data_t;

    flit_data_t                         fifo_data_in;
    flit_data_t                         fifo_data_out;

    wire [VC_NUM-1:0]                   fifo_write;
    wire [VC_NUM-1:0]                   fifo_read;
    wire [VC_NUM-1:0]                   fifo_empty;
    wire [VC_NUM-1:0]                   fifo_full;
    wire [LOG2_DEPTH:0]                 fifo_count [0:VC_NUM-1];

    reg  [VC_NUM-1:0]                   alloc_vc;
    reg  [VC_NUM-1:0]                   credit_out_reg;
    wire [VC_NUM-1:0]                   credit_in_sync;

    integer i;

    assign flit_data = {fifo_data_out.data, fifo_data_out.pkt_id, fifo_data_out.prio, fifo_data_out.vc_id};
    assign flit_out = ~(&fifo_empty);
    assign credit_in_sync = credit_in;

    assign fifo_data_in = '{data: data_in, pkt_id: pkt_id_in, prio: prio_in, vc_id: vc_id_in};

    generate
        for (i = 0; i < VC_NUM; i = i + 1) begin : VC_FIFO
            fifo_sync #
            (
                .DEPTH      (VC_DEPTH),
                .WIDTH      (DATA_WIDTH + VC_NUM + PRIO_WIDTH + PKT_ID_WIDTH),
                .PROTECTED  (1)
            )
            vc_fifo
            (
                .clk        (clk),
                .rst_n      (rst_n),

                .wr_en      (fifo_write[i] && valid_in),
                .wr_data    (fifo_data_in),
                .full       (fifo_full[i]),

                .rd_en      (fifo_read[i] && ready_in),
                .rd_data    (fifo_data_out),
                .empty      (fifo_empty[i]),

                .count      (fifo_count[i])
            );
        end
    endgenerate

    always @(*) begin
        fifo_write = {VC_NUM{1'b0}};
        fifo_read  = {VC_NUM{1'b0}};

        for (i = 0; i < VC_NUM; i = i + 1) begin
            if (valid_in && (alloc_vc[i] || vc_id_in[i])) begin
                fifo_write[i] = 1'b1;
            end
            if (ready_in && ~fifo_empty[i] && alloc_vc[i]) begin
                fifo_read[i] = 1'b1;
            end
        end
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            alloc_vc <= {VC_NUM{1'b0}};
        end else begin
            alloc_vc <= alloc_vc;
            for (i = 0; i < VC_NUM; i = i + 1) begin
                if (valid_in && vc_id_in[i] && ~fifo_full[i]) begin
                    alloc_vc[i] <= 1'b1;
                end else if (ready_in && alloc_vc[i] && ~fifo_empty[i]) begin
                    alloc_vc[i] <= 1'b0;
                end
            end
        end
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            credit_out_reg <= {VC_NUM{1'b0}};
        end else begin
            credit_out_reg <= credit_in_sync;
        end
    end

    assign credit_out = credit_out_reg;
    assign vc_status = {fifo_full[3], fifo_full[2], fifo_full[1], fifo_full[0],
                        fifo_empty[3], fifo_empty[2], fifo_empty[1], fifo_empty[0]};

endmodule

module fifo_sync #
(
    parameter DEPTH      = 16,
    parameter WIDTH      = 512,
    parameter PROTECTED  = 1,
    parameter FWFT       = 0
)
(
    input  wire                         clk,
    input  wire                         rst_n,

    input  wire                         wr_en,
    input  wire [WIDTH-1:0]             wr_data,
    output wire                         full,

    input  wire                         rd_en,
    output wire [WIDTH-1:0]             rd_data,
    output wire                         empty,

    output wire [LOG2_DEPTH:0]          count
);

    localparam LOG2_DEPTH = $clog2(DEPTH);

    reg  [WIDTH-1:0]                    mem     [0:DEPTH-1];
    reg  [LOG2_DEPTH-1:0]              wr_ptr;
    reg  [LOG2_DEPTH-1:0]              rd_ptr;
    reg  [LOG2_DEPTH:0]                count_reg;
    wire                               wr_en_safe;
    wire                               rd_en_safe;

    assign full  = (count_reg == DEPTH);
    assign empty = (count_reg == 0);
    assign count = count_reg;

    generate
        if (PROTECTED == 1) begin : PROT_FIFO
            assign wr_en_safe = wr_en && ~full;
            assign rd_en_safe = rd_en && ~empty;
        end else begin : UNPROT_FIFO
            assign wr_en_safe = wr_en;
            assign rd_en_safe = rd_en;
        end
    endgenerate

    always @(posedge clk) begin
        if (wr_en_safe) begin
            mem[wr_ptr] <= wr_data;
        end
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_ptr <= {LOG2_DEPTH{1'b0}};
            rd_ptr <= {LOG2_DEPTH{1'b0}};
            count_reg <= {LOG2_DEPTH+1{1'b0}};
        end else begin
            if (wr_en_safe) begin
                wr_ptr <= wr_ptr + 1'b1;
            end
            if (rd_en_safe) begin
                rd_ptr <= rd_ptr + 1'b1;
            end
            if (wr_en_safe && ~rd_en_safe) begin
                count_reg <= count_reg + 1'b1;
            end else if (~wr_en_safe && rd_en_safe) begin
                count_reg <= count_reg - 1'b1;
            end
        end
    end

    generate
        if (FWFT == 1) begin : FWFT_MODE
            assign rd_data = mem[rd_ptr];
        end else begin : NORMAL_MODE
            always @(posedge clk) begin
                if (rd_en_safe) begin
                    rd_data <= mem[rd_ptr];
                end
            end
        end
    endgenerate

endmodule
