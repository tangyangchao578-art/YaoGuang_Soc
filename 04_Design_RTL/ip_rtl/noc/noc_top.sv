`timescale 1ps/1ps

module noc_top #
(
    parameter NUM_PORTS      = 64,
    parameter DATA_WIDTH     = 512,
    parameter VC_NUM         = 4,
    parameter VC_DEPTH       = 16,
    parameter PRIO_WIDTH     = 2,
    parameter PKT_ID_WIDTH   = 8,
    parameter CLK_PERIOD_PS  = 500
)
(
    input  wire                         clk,
    input  wire                         rst_n,

    input  wire [NUM_PORTS-1:0]         vc_valid_in   [0:NUM_PORTS-1],
    input  wire [DATA_WIDTH-1:0]        vc_data_in    [0:NUM_PORTS-1],
    input  wire [VC_NUM-1:0]            vc_id_in      [0:NUM_PORTS-1],
    input  wire [PRIO_WIDTH-1:0]        vc_prio_in    [0:NUM_PORTS-1],
    input  wire [PKT_ID_WIDTH-1:0]      vc_pkt_id_in  [0:NUM_PORTS-1],

    output wire [NUM_PORTS-1:0]         vc_valid_out  [0:NUM_PORTS-1],
    output wire [DATA_WIDTH-1:0]        vc_data_out   [0:NUM_PORTS-1],
    output wire [VC_NUM-1:0]            vc_id_out     [0:NUM_PORTS-1],
    output wire [PRIO_WIDTH-1:0]        vc_prio_out   [0:NUM_PORTS-1],
    output wire [PKT_ID_WIDTH-1:0]      vc_pkt_id_out [0:NUM_PORTS-1],

    output wire [NUM_PORTS-1:0]         port_busy,
    output wire [NUM_PORTS*VC_NUM-1:0]  vc_credits,

    output wire [7:0]                   sys_status,
    output wire                         sys_error
);

    localparam FLIT_WIDTH = DATA_WIDTH + VC_NUM + PRIO_WIDTH + PKT_ID_WIDTH + 1;

    wire [NUM_PORTS-1:0]                 sw_valid_in  [0:NUM_PORTS-1];
    wire [FLIT_WIDTH-1:0]                sw_data_in   [0:NUM_PORTS-1];
    wire [NUM_PORTS-1:0]                 sw_ready_out [0:NUM_PORTS-1];

    wire [NUM_PORTS-1:0]                 sw_valid_out [0:NUM_PORTS-1];
    wire [FLIT_WIDTH-1:0]                sw_data_out  [0:NUM_PORTS-1];
    wire [NUM_PORTS-1:0]                 sw_ready_in  [0:NUM_PORTS-1];

    wire [NUM_PORTS-1:0]                 arb_grant    [0:NUM_PORTS-1];
    wire [NUM_PORTS*VC_NUM-1:0]          credit_in;
    wire [NUM_PORTS*VC_NUM-1:0]          credit_out;

    genvar i, j;

    generate
        for (i = 0; i < NUM_PORTS; i = i + 1) begin : INPUT_PORT_GEN
            virtual_channel #
            (
                .VC_NUM        (VC_NUM),
                .VC_DEPTH      (VC_DEPTH),
                .DATA_WIDTH    (DATA_WIDTH),
                .PRIO_WIDTH    (PRIO_WIDTH),
                .PKT_ID_WIDTH  (PKT_ID_WIDTH)
            )
            vc_inst
            (
                .clk            (clk),
                .rst_n          (rst_n),

                .valid_in       (vc_valid_in[i]),
                .data_in        (vc_data_in[i]),
                .vc_id_in       (vc_id_in[i]),
                .prio_in        (vc_prio_in[i]),
                .pkt_id_in      (vc_pkt_id_in[i]),

                .flit_out       (sw_data_in[i]),
                .valid_out      (sw_valid_in[i]),
                .ready_in       (sw_ready_out[i]),

                .credit_in      (credit_in[i*VC_NUM +: VC_NUM]),
                .credit_out     (credit_out[i*VC_NUM +: VC_NUM]),

                .vc_status      (port_busy[i])
            );

            assign credit_in[i*VC_NUM +: VC_NUM] = credit_out[i*VC_NUM +: VC_NUM];
        end
    endgenerate

    crossbar_64port #
    (
        .NUM_PORTS     (NUM_PORTS),
        .DATA_WIDTH    (FLIT_WIDTH),
        .VC_NUM        (VC_NUM),
        .VC_DEPTH      (VC_DEPTH)
    )
    xbar_inst
    (
        .clk           (clk),
        .rst_n         (rst_n),

        .valid_in      (sw_valid_in),
        .data_in       (sw_data_in),
        .ready_out     (sw_ready_out),

        .valid_out     (sw_valid_out),
        .data_out      (sw_data_out),
        .ready_in      (sw_ready_in),

        .prio_in       (vc_prio_in),

        .arb_grant     (arb_grant),

        .credit_in     (credit_out),
        .credit_out    (credit_in),

        .sys_error     (sys_error)
    );

    generate
        for (i = 0; i < NUM_PORTS; i = i + 1) begin : OUTPUT_PORT_GEN
            wire [FLIT_WIDTH-1:0]               flit_data;
            wire                                flit_valid;

            assign flit_data  = sw_data_out[i];
            assign flit_valid = sw_valid_out[i];

            assign {vc_valid_out[i], vc_prio_out[i], vc_id_out[i], vc_pkt_id_out[i], vc_data_out[i]} = flit_data;

            assign sw_ready_in[i] = 1'b1;
        end
    endgenerate

    assign vc_credits = credit_out;
    assign sys_status = {port_busy[7:0]};

endmodule
