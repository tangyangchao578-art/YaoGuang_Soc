`timescale 1ps/1ps

module qos_arbiter #
(
    parameter NUM_PORTS     = 64,
    parameter NUM_VC        = 4,
    parameter PRIO_WIDTH    = 2,
    parameter ARB_TYPE      = "WRR",
    parameter MAX_RATE      = 1000000000,
    parameter CLK_PERIOD_PS = 500
)
(
    input  wire                         clk,
    input  wire                         rst_n,

    input  wire [NUM_PORTS-1:0]         req_valid,
    input  wire [NUM_PORTS-1:0][PRIO_WIDTH-1:0] req_prio,
    input  wire [NUM_PORTS-1:0][31:0]   req_rate,
    output wire [NUM_PORTS-1:0]         req_ready,

    output wire [NUM_PORTS-1:0]         grant_valid,
    output wire [NUM_PORTS-1:0]         grant_prio,
    output wire [NUM_PORTS-1:0][LOG2_PORTS-1:0] grant_port,
    input  wire [NUM_PORTS-1:0]         grant_ack,

    input  wire [NUM_PORTS-1:0][31:0]   token_bucket,
    output wire [NUM_PORTS-1:0][31:0]   token_update,

    output wire [7:0]                   arb_status
);

    localparam LOG2_PORTS = $clog2(NUM_PORTS);
    localparam LOG2_PRIO  = $clog2(2**PRIO_WIDTH);

    wire [NUM_PORTS-1:0]                req_active;
    wire [NUM_PORTS-1:0]                prio_mask [0:2**PRIO_WIDTH-1];

    reg  [PRIO_WIDTH-1:0]               rr_arb_ptr [0:NUM_PORTS-1];
    reg  [NUM_PORTS-1:0]                wrr_weight [0:NUM_PORTS-1];
    reg  [NUM_PORTS-1:0]                wrr_count  [0:NUM_PORTS-1];

    reg  [31:0]                         token_reg  [0:NUM_PORTS-1];
    reg  [31:0]                         rate_limit [0:NUM_PORTS-1];

    reg  [7:0]                          status_reg;

    integer i, j, k;

    assign req_active = req_valid & req_ready;
    assign grant_valid = req_active;
    assign arb_status = status_reg;

    generate
        for (i = 0; i < NUM_PORTS; i = i + 1) begin : TOKEN_BUCKET
            always @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    token_reg[i] <= 32'd0;
                end else begin
                    token_reg[i] <= token_reg[i] + req_rate[i];
                    if (grant_valid[i]) begin
                        token_reg[i] <= token_reg[i] - 32'd64;
                    end
                end
            end
            assign token_update[i] = token_reg[i];
        end
    endgenerate

    generate
        if (ARB_TYPE == "RR_PRIO") begin : RR_PRIO_ARB
            for (i = 0; i < NUM_PORTS; i = i + 1) begin : RR_PRIO_INST
                round_robin_prio #
                (
                    .NUM_PORTS (NUM_PORTS)
                )
                rrp_inst
                (
                    .clk       (clk),
                    .rst_n     (rst_n),
                    .req_in    (req_valid),
                    .prio_in   (req_prio),
                    .ptr_in    (rr_arb_ptr[i]),
                    .grant_out (grant_port[i]),
                    .grant_prio (grant_prio[i])
                );
            end
        end else if (ARB_TYPE == "WRR") begin : WRR_ARB
            for (i = 0; i < NUM_PORTS; i = i + 1) begin : WRR_INST
                weighted_rr_arbiter #
                (
                    .NUM_PORTS (NUM_PORTS)
                )
                wrr_inst
                (
                    .clk       (clk),
                    .rst_n     (rst_n),
                    .req_in    (req_valid),
                    .weight_in (wrr_weight[i]),
                    .ptr_in    (wrr_count[i]),
                    .grant_out (grant_port[i])
                );
            end
        end else begin : PRIO_ONLY
            for (i = 0; i < NUM_PORTS; i = i + 1) begin : PRIO_INST
                fixed_prio_arbiter #
                (
                    .NUM_PORTS (NUM_PORTS)
                )
                fpa_inst
                (
                    .req_in   (req_valid),
                    .grant_out (grant_port[i])
                );
            end
        end
    endgenerate

    generate
        for (i = 0; i < NUM_PORTS; i = i + 1) begin : PTR_UPDATE
            always @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    rr_arb_ptr[i] <= {PRIO_WIDTH{1'b0}};
                    wrr_count[i] <= {NUM_PORTS{1'b0}};
                end else begin
                    if (grant_ack[i]) begin
                        rr_arb_ptr[i] <= grant_port[i][PRIO_WIDTH-1:0];
                        wrr_count[i] <= grant_port[i];
                    end
                end
            end
        end
    endgenerate

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            status_reg <= 8'd0;
        end else begin
            status_reg[7] <= |grant_valid;
            status_reg[6:0] <= 7'd0;
        end
    end

endmodule

module round_robin_prio #
(
    parameter NUM_PORTS = 64
)
(
    input  wire                         clk,
    input  wire                         rst_n,
    input  wire [NUM_PORTS-1:0]         req_in,
    input  wire [NUM_PORTS-1:0][1:0]    prio_in,
    input  wire [PRIO_WIDTH-1:0]        ptr_in,
    output wire [NUM_PORTS-1:0]         grant_out,
    output wire [PRIO_WIDTH-1:0]        grant_prio
);

    wire [NUM_PORTS-1:0]                prio_masked [0:2**PRIO_WIDTH-1];
    wire [NUM_PORTS-1:0]                grant_masked [0:2**PRIO_WIDTH-1];

    assign grant_out = |grant_masked;
    assign grant_prio = ptr_in;

    generate
        for (genvar g = 0; g < 2**PRIO_WIDTH; g = g + 1) begin : PRIO_GRP
            mask_arbiter #
            (
                .NUM_PORTS (NUM_PORTS)
            )
            ma_inst
            (
                .req_in   (req_in),
                .mask_in  (prio_masked[g]),
                .grant_out (grant_masked[g])
            );
        end
    endgenerate

endmodule

module weighted_rr_arbiter #
(
    parameter NUM_PORTS = 64
)
(
    input  wire                         clk,
    input  wire                         rst_n,
    input  wire [NUM_PORTS-1:0]         req_in,
    input  wire [NUM_PORTS-1:0]         weight_in,
    input  wire [NUM_PORTS-1:0]         ptr_in,
    output wire [NUM_PORTS-1:0]         grant_out
);

    reg  [NUM_PORTS-1:0]                wrr_ptr;
    reg  [NUM_PORTS-1:0]                wrr_remain;
    wire [NUM_PORTS-1:0]                active_req;

    assign active_req = req_in;
    assign grant_out = active_req & wrr_ptr;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wrr_ptr <= {NUM_PORTS{1'b1}};
            wrr_remain <= {NUM_PORTS{1'b0}};
        end else begin
            if (grant_out != {NUM_PORTS{1'b0}}) begin
                wrr_remain <= weight_in;
                wrr_ptr <= grant_out;
            end else if (wrr_remain > 0) begin
                wrr_remain <= wrr_remain - 1'b1;
            end else begin
                wrr_ptr <= active_req;
                wrr_remain <= weight_in;
            end
        end
    end

endmodule

module mask_arbiter #
(
    parameter NUM_PORTS = 64
)
(
    input  wire [NUM_PORTS-1:0]         req_in,
    input  wire [NUM_PORTS-1:0]         mask_in,
    output wire [NUM_PORTS-1:0]         grant_out
);

    wire [NUM_PORTS-1:0]                masked_req;

    assign masked_req = req_in & mask_in;

    fixed_prio_arbiter #
    (
        .NUM_PORTS (NUM_PORTS)
    )
    fpa
    (
        .req   (masked_req),
        .grant (grant_out)
    );

endmodule

module fixed_prio_arbiter #
(
    parameter NUM_PORTS = 64
)
(
    input  wire [NUM_PORTS-1:0]         req,
    output wire [NUM_PORTS-1:0]         grant
);

    integer i;
    reg  [NUM_PORTS-1:0]                grant_reg;

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

module token_bucket_rate_limiter #
(
    parameter DATA_WIDTH = 32,
    parameter MAX_BURST  = 1024
)
(
    input  wire                         clk,
    input  wire                         rst_n,
    input  wire [DATA_WIDTH-1:0]        rate,
    input  wire [DATA_WIDTH-1:0]        burst,

    input  wire                         pkt_valid,
    output wire                         pkt_ready,
    input  wire [DATA_WIDTH-1:0]        pkt_size,

    output wire [DATA_WIDTH-1:0]        token_count,
    output wire                         rate_exceeded
);

    localparam MAX_TOKENS = MAX_BURST;

    reg  [DATA_WIDTH-1:0]               tokens;
    reg                                 ready_reg;

    assign pkt_ready = ready_reg;
    assign token_count = tokens;
    assign rate_exceeded = pkt_valid && (tokens < pkt_size);

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            tokens <= MAX_TOKENS[DATA_WIDTH-1:0];
            ready_reg <= 1'b1;
        end else begin
            tokens <= tokens + rate;
            if (tokens > MAX_TOKENS) begin
                tokens <= MAX_TOKENS[DATA_WIDTH-1:0];
            end

            if (pkt_valid && pkt_ready) begin
                tokens <= tokens - pkt_size;
                ready_reg <= 1'b0;
            end else begin
                ready_reg <= (tokens >= pkt_size);
            end
        end
    end

endmodule

module latency_budget_monitor #
(
    parameter NUM_PORTS     = 64,
    parameter MAX_LATENCY   = 100,
    parameter CNT_WIDTH     = 8
)
(
    input  wire                         clk,
    input  wire                         rst_n,

    input  wire [NUM_PORTS-1:0]         pkt_in,
    input  wire [NUM_PORTS-1:0]         pkt_out,
    input  wire [NUM_PORTS-1:0][CNT_WIDTH-1:0] pkt_latency,

    output wire [NUM_PORTS-1:0]         lat_exceeded,
    output wire [7:0]                   max_latency
);

    reg  [CNT_WIDTH-1:0]                max_lat_reg;

    generate
        for (genvar i = 0; i < NUM_PORTS; i = i + 1) begin : LAT_CHECK
            assign lat_exceeded[i] = (pkt_latency[i] > MAX_LATENCY[CNT_WIDTH-1:0]);
        end
    endgenerate

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            max_lat_reg <= {CNT_WIDTH{1'b0}};
        end else begin
            if (|pkt_latency) begin
                max_lat_reg <= max_lat_reg | pkt_latency;
            end
        end
    end

    assign max_latency = max_lat_reg[7:0];

endmodule
