`timescale 1ps/1ps

module flow_control #
(
    parameter NUM_PORTS     = 64,
    parameter VC_NUM        = 4,
    parameter CREDIT_WIDTH  = 4
)
(
    input  wire                         clk,
    input  wire                         rst_n,

    input  wire [NUM_PORTS-1:0]         rx_valid,
    input  wire [NUM_PORTS-1:0]         rx_data,
    output wire [NUM_PORTS-1:0]         rx_ready,

    output wire [NUM_PORTS-1:0]         tx_valid,
    output wire [NUM_PORTS-1:0]         tx_data,
    input  wire [NUM_PORTS-1:0]         tx_ready,

    input  wire [NUM_PORTS*VC_NUM-1:0]  local_credit_in,
    output wire [NUM_PORTS*VC_NUM-1:0]  local_credit_out,

    output wire [NUM_PORTS-1:0]         pause_frame,
    output wire [7:0]                   error_status
);

    localparam LOG2_PORTS = $clog2(NUM_PORTS);
    localparam LOG2_VC    = $clog2(VC_NUM);

    reg  [CREDIT_WIDTH-1:0]             credit_count [0:NUM_PORTS-1][0:VC_NUM-1];
    wire [VC_NUM-1:0]                   credit_avail [0:NUM_PORTS-1];
    wire [VC_NUM-1:0]                   credit_update [0:NUM_PORTS-1];

    reg  [NUM_PORTS-1:0]                pause_reg;
    wire [NUM_PORTS-1:0]                pause_req;

    wire [NUM_PORTS-1:0]                link_error;
    wire [NUM_PORTS-1:0]                crc_error;

    reg  [7:0]                          error_reg;

    integer i, j;

    assign pause_frame = pause_reg;

    generate
        for (i = 0; i < NUM_PORTS; i = i + 1) begin : CREDIT_TRACK
            for (j = 0; j < VC_NUM; j = j + 1) begin : VC_CREDIT
                always @(posedge clk or negedge rst_n) begin
                    if (!rst_n) begin
                        credit_count[i][j] <= {CREDIT_WIDTH{1'b0}};
                    end else begin
                        if (tx_ready[i] && tx_valid[i]) begin
                            credit_count[i][j] <= credit_count[i][j] - 1'b1;
                        end
                        if (rx_valid[i] && rx_ready[i]) begin
                            credit_count[i][j] <= credit_count[i][j] + 1'b1;
                        end
                    end
                end

                assign credit_avail[i][j] = (credit_count[i][j] > 0);
                assign credit_update[i][j] = rx_valid[i] && rx_ready[i];
            end
        end
    endgenerate

    generate
        for (i = 0; i < NUM_PORTS; i = i + 1) begin : RX_PATH
            assign rx_ready[i] = pause_req[i] ? 1'b0 : 1'b1;
            assign tx_valid[i] = rx_valid[i] && ~pause_reg[i];
            assign tx_data[i] = rx_data[i];

            always @(*) begin
                pause_req[i] = 1'b0;
                for (j = 0; j < VC_NUM; j = j + 1) begin
                    if (credit_count[i][j] == 0) begin
                        pause_req[i] = 1'b1;
                    end
                end
            end
        end
    endgenerate

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            pause_reg <= {NUM_PORTS{1'b0}};
        end else begin
            pause_reg <= pause_req;
        end
    end

    generate
        for (i = 0; i < NUM_PORTS; i = i + 1) begin : ERROR_DETECT
            crc_checker #
            (
                .DATA_WIDTH (512)
            )
            crc_inst
            (
                .clk        (clk),
                .rst_n      (rst_n),
                .data_in    (rx_data[i]),
                .valid_in   (rx_valid[i]),
                .crc_error  (crc_error[i])
            );

            always @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    error_reg <= 8'd0;
                end else begin
                    if (crc_error[i]) begin
                        error_reg[i] <= 1'b1;
                    end
                end
            end
        end
    endgenerate

    assign local_credit_out = local_credit_in;
    assign error_status = error_reg;

endmodule

module credit_based_fc #
(
    parameter NUM_PORTS  = 64,
    parameter VC_NUM     = 4,
    parameter CREDIT_WID = 4
)
(
    input  wire                         clk,
    input  wire                         rst_n,

    input  wire [NUM_PORTS-1:0]         upstream_valid,
    output wire [NUM_PORTS-1:0]         upstream_ready,

    output wire [NUM_PORTS-1:0]         downstream_valid,
    input  wire [NUM_PORTS-1:0]         downstream_ready,

    input  wire [NUM_PORTS*VC_NUM-1:0]  downstream_credit,
    output wire [NUM_PORTS*VC_NUM-1:0]  upstream_credit,

    output wire [NUM_PORTS-1:0]         flow_ctrl_active
);

    localparam MAX_CREDIT = 16;

    reg  [CREDIT_WID-1:0]               credit_cnt_PORTS-1 [0:NUM][0:VC_NUM-1];
    wire [VC_NUM-1:0]                   has_credit [0:NUM_PORTS-1];

    integer i, j;

    assign flow_ctrl_active = ~has_credit;

    generate
        for (i = 0; i < NUM_PORTS; i = i + 1) begin : PORT_FC
            assign upstream_ready[i] = &has_credit[i];
            assign downstream_valid[i] = upstream_valid[i];

            for (j = 0; j < VC_NUM; j = j + 1) begin : VC_CREDIT
                assign has_credit[i][j] = (credit_cnt[i][j] > 0);

                always @(posedge clk or negedge rst_n) begin
                    if (!rst_n) begin
                        credit_cnt[i][j] <= MAX_CREDIT[CREDIT_WID-1:0];
                    end else begin
                        if (upstream_valid[i] && upstream_ready[i]) begin
                            credit_cnt[i][j] <= credit_cnt[i][j] - 1'b1;
                        end
                        if (downstream_ready[i] && downstream_valid[i]) begin
                            credit_cnt[i][j] <= credit_cnt[i][j] + 1'b1;
                        end
                    end
                end
            end
        end
    endgenerate

    assign upstream_credit = downstream_credit;

endmodule

module pause_frame_gen #
(
    parameter NUM_PORTS = 64
)
(
    input  wire                         clk,
    input  wire                         rst_n,

    input  wire [NUM_PORTS-1:0]         pause_req,
    input  wire [15:0]                  pause_quanta,

    output wire [NUM_PORTS-1:0]         pause_frame,
    output wire                         pause_valid
);

    localparam PAUSE_STATE_IDLE  = 2'b00;
    localparam PAUSE_STATE_SEND  = 2'b01;
    localparam PAUSE_STATE_WAIT  = 2'b10;

    reg  [1:0]                          state;
    reg  [15:0]                         quanta_reg;
    integer                             pause_cnt;

    assign pause_valid = (state == PAUSE_STATE_SEND);

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= PAUSE_STATE_IDLE;
            quanta_reg <= 16'd0;
        end else begin
            case (state)
                PAUSE_STATE_IDLE: begin
                    if (|pause_req) begin
                        state <= PAUSE_STATE_SEND;
                        quanta_reg <= pause_quanta;
                    end
                end
                PAUSE_STATE_SEND: begin
                    state <= PAUSE_STATE_WAIT;
                end
                PAUSE_STATE_WAIT: begin
                    if (quanta_reg > 0) begin
                        quanta_reg <= quanta_reg - 1'b1;
                    end else begin
                        state <= PAUSE_STATE_IDLE;
                    end
                end
            endcase
        end
    end

    generate
        for (pause_cnt = 0; pause_cnt < NUM_PORTS; pause_cnt = pause_cnt + 1) begin : PAUSE_OUT
            assign pause_frame[pause_cnt] = (state == PAUSE_STATE_SEND) && pause_req[pause_cnt];
        end
    endgenerate

endmodule

module crc_checker #
(
    parameter DATA_WIDTH = 512
)
(
    input  wire                         clk,
    input  wire                         rst_n,
    input  wire [DATA_WIDTH-1:0]        data_in,
    input  wire                         valid_in,
    output wire                         crc_error
);

    wire [31:0]                         calc_crc;
    wire [31:0]                         recv_crc;

    crc32_generator #
    (
        .DATA_WIDTH (DATA_WIDTH)
    )
    crc_gen
    (
        .data_in   (data_in),
        .crc_out   (calc_crc)
    );

    assign recv_crc = data_in[31:0];
    assign crc_error = valid_in && (calc_crc != recv_crc);

endmodule

module crc32_generator #
(
    parameter DATA_WIDTH = 512
)
(
    input  wire [DATA_WIDTH-1:0]        data_in,
    output wire [31:0]                  crc_out
);

    integer i;
    reg  [31:0]                         crc_reg;
    wire [31:0]                         next_crc;

    assign crc_out = crc_reg;

    always @(*) begin
        crc_reg = 32'hFFFFFFFF;
        for (i = 0; i < DATA_WIDTH/8; i = i + 1) begin
            crc_reg = next_crc_table({crc_reg[31:24], data_in[i*8 +: 8]});
        end
    end

    function [31:0] next_crc_table;
        input [31:0] cur_crc;
        input [7:0]  byte_in;
        reg   [23:0] tmp;
        begin
            tmp = cur_crc ^ byte_in;
            next_crc_table = cur_crc >> 8;
        end
    endfunction

endmodule
