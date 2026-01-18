`timescale 1ps/1ps

module crossbar_64port #
(
    parameter NUM_PORTS     = 64,
    parameter DATA_WIDTH    = 528,
    parameter VC_NUM        = 4,
    parameter VC_DEPTH      = 16,
    parameter ARB_TYPE      = "RR_PRIO",
    parameter OUTPUT_REG    = 1
)
(
    input  wire                         clk,
    input  wire                         rst_n,

    input  wire [NUM_PORTS-1:0]         valid_in    [0:NUM_PORTS-1],
    input  wire [DATA_WIDTH-1:0]        data_in     [0:NUM_PORTS-1],
    output wire [NUM_PORTS-1:0]         ready_out   [0:NUM_PORTS-1],

    output wire [NUM_PORTS-1:0]         valid_out   [0:NUM_PORTS-1],
    input  wire [NUM_PORTS-1:0]         ready_in    [0:NUM_PORTS-1],
    input  wire [DATA_WIDTH-1:0]        data_out    [0:NUM_PORTS-1],

    input  wire [NUM_PORTS-1:0][1:0]    prio_in,

    output wire [NUM_PORTS-1:0]         arb_grant   [0:NUM_PORTS-1],

    input  wire [NUM_PORTS*VC_NUM-1:0]  credit_in,
    output wire [NUM_PORTS*VC_NUM-1:0]  credit_out,

    output wire                         sys_error
);

    localparam REQ_WIDTH   = NUM_PORTS;
    localparam GRANT_WIDTH = NUM_PORTS;
    localparam LOG2_PORTS  = $clog2(NUM_PORTS);

    wire [NUM_PORTS-1:0]                 req_out     [0:NUM_PORTS-1];
    wire [NUM_PORTS-1:0]                 req_in      [0:NUM_PORTS-1];
    wire [NUM_PORTS-1:0]                 grant_out   [0:NUM_PORTS-1];
    wire [NUM_PORTS-1:0]                 grant_in    [0:NUM_PORTS-1];

    wire [NUM_PORTS-1:0][DATA_WIDTH-1]   xbar_data_in;
    wire [NUM_PORTS-1:0][DATA_WIDTH-1]   xbar_data_out;

    wire [NUM_PORTS-1:0][VC_NUM-1:0]     vc_credit_in;
    wire [NUM_PORTS-1:0][VC_NUM-1:0]     vc_credit_out;

    wire [NUM_PORTS-1:0]                 sw_valid_reg;
    wire [NUM_PORTS-1:0][DATA_WIDTH-1]   sw_data_reg;
    wire [NUM_PORTS-1:0]                 sw_ready_reg;

    reg  [NUM_PORTS-1:0]                 rr_arb_ptr [0:NUM_PORTS-1];
    reg  [NUM_PORTS-1:0]                 prio_arb_ptr [0:NUM_PORTS-1];

    integer i, j, k;

    assign sys_error = 1'b0;

    generate
        for (i = 0; i < NUM_PORTS; i = i + 1) begin : PORT_CONN
            assign xbar_data_in[i] = data_in[i];
            assign data_out[i]     = xbar_data_out[i];
            assign ready_out[i]    = sw_ready_reg[i];
            assign valid_out[i]    = sw_valid_reg[i];
            assign arb_grant[i]    = grant_out[i];

            for (j = 0; j < VC_NUM; j = j + 1) begin : CREDIT_CONN
                assign vc_credit_in[i][j] = credit_in[i*VC_NUM + j];
                assign credit_out[i*VC_NUM + j] = vc_credit_out[i][j];
            end
        end
    endgenerate

    generate
        for (i = 0; i < NUM_PORTS; i = i + 1) begin : INPUT_ARB
            always @(*) begin
                req_in[i] = {NUM_PORTS{1'b0}};
                for (j = 0; j < NUM_PORTS; j = j + 1) begin
                    if (valid_in[j] && prio_in[j] == i[1:0]) begin
                        req_in[i][j] = 1'b1;
                    end
                end
            end

            round_robin_arbiter #
            (
                .NUM_PORTS (NUM_PORTS)
            )
            rr_arb_inst
            (
                .clk       (clk),
                .rst_n     (rst_n),
                .req       (req_in[i]),
                .prio      (prio_arb_ptr[i]),
                .grant     (grant_in[i]),
                .valid     (valid_in[i]),
                .ready     (ready_in[i])
            );
        end
    endgenerate

    crossbar_matrix #
    (
        .NUM_PORTS  (NUM_PORTS),
        .DATA_WIDTH (DATA_WIDTH)
    )
    xbar_inst
    (
        .select    (grant_in),
        .data_in   (xbar_data_in),
        .data_out  (xbar_data_out)
    );

    generate
        if (OUTPUT_REG == 1) begin : OUT_REG
            always @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    sw_valid_reg <= {NUM_PORTS{1'b0}};
                    sw_data_reg  <= {NUM_PORTS*DATA_WIDTH{1'b0}};
                    sw_ready_reg <= {NUM_PORTS{1'b0}};
                end else begin
                    for (i = 0; i < NUM_PORTS; i = i + 1) begin
                        sw_valid_reg[i] <= valid_in[i] && grant_in[i];
                        sw_data_reg[i]  <= xbar_data_out[i];
                        sw_ready_reg[i] <= ready_in[i];
                    end
                end
            end
        end else begin : NO_OUT_REG
            always @(*) begin
                for (i = 0; i < NUM_PORTS; i = i + 1) begin
                    sw_valid_reg[i] = valid_in[i] && grant_in[i];
                    sw_data_reg[i]  = xbar_data_out[i];
                    sw_ready_reg[i] = ready_in[i];
                end
            end
        end
    endgenerate

    generate
        for (i = 0; i < NUM_PORTS; i = i + 1) begin : RR_PTR_UPDATE
            always @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    rr_arb_ptr[i] <= {NUM_PORTS{1'b0}};
                    prio_arb_ptr[i] <= {NUM_PORTS{1'b0}};
                end else begin
                    if (grant_in[i] != {NUM_PORTS{1'b0}}) begin
                        rr_arb_ptr[i] <= grant_in[i];
                        prio_arb_ptr[i] <= grant_in[i];
                    end
                end
            end
        end
    endgenerate

    generate
        for (i = 0; i < NUM_PORTS; i = i + 1) begin : VC_CREDIT_FLOW
            for (j = 0; j < NUM_PORTS; j = j + 1) begin
                assign vc_credit_out[i][j] = vc_credit_in[i][j];
            end
        end
    endgenerate

endmodule

module round_robin_arbiter #
(
    parameter NUM_PORTS = 64
)
(
    input  wire                     clk,
    input  wire                     rst_n,
    input  wire [NUM_PORTS-1:0]     req,
    input  wire [NUM_PORTS-1:0]     prio,
    output wire [NUM_PORTS-1:0]     grant,
    input  wire                     valid,
    input  wire                     ready
);

    wire [NUM_PORTS-1:0]            req_masked;
    wire [NUM_PORTS-1:0]            req_unmasked;
    wire [NUM_PORTS-1:0]            grant_masked;
    wire [NUM_PORTS-1:0]            grant_unmasked;

    assign req_unmasked = req;
    assign grant = grant_masked | grant_unmasked;

    fixed_prio_arbiter #
    (
        .NUM_PORTS (NUM_PORTS)
    )
    fpa_masked
    (
        .req       (req_masked),
        .grant     (grant_masked)
    );

    fixed_prio_arbiter #
    (
        .NUM_PORTS (NUM_PORTS)
    )
    fpa_unmasked
    (
        .req       (req_unmasked),
        .grant     (grant_unmasked)
    );

endmodule

module fixed_prio_arbiter #
(
    parameter NUM_PORTS = 64
)
(
    input  wire [NUM_PORTS-1:0]     req,
    output wire [NUM_PORTS-1:0]     grant
);

    integer i;
    reg [NUM_PORTS-1:0]             grant_reg;

    always @(*) begin
        grant_reg = {NUM_PORTS{1'b0}};
        for (i = 0; i < NUM_PORTS; i = i + 1) begin
            if (req[i]) begin
                grant_reg[i] = 1'b1;
                disable fixed_prio_arbiter;
            end
        end
    end

    assign grant = grant_reg;

endmodule

module crossbar_matrix #
(
    parameter NUM_PORTS  = 64,
    parameter DATA_WIDTH = 528
)
(
    input  wire [NUM_PORTS-1:0]             select  [0:NUM_PORTS-1],
    input  wire [NUM_PORTS-1:0][DATA_WIDTH-1:0] data_in,
    output wire [NUM_PORTS-1:0][DATA_WIDTH-1:0] data_out
);

    integer i, j;

    always @(*) begin
        for (i = 0; i < NUM_PORTS; i = i + 1) begin
            data_out[i] = {DATA_WIDTH{1'b0}};
            for (j = 0; j < NUM_PORTS; j = j + 1) begin
                if (select[i][j]) begin
                    data_out[i] = data_in[j];
                end
            end
        end
    end

endmodule
