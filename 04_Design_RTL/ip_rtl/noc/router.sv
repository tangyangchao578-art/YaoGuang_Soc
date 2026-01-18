`timescale 1ps/1ps

module router #
(
    parameter NUM_PORTS      = 5,
    parameter DATA_WIDTH     = 512,
    parameter VC_NUM         = 4,
    parameter VC_DEPTH       = 16,
    parameter PRIO_WIDTH     = 2,
    parameter PKT_ID_WIDTH   = 8,
    parameter ROUTE_TYPE     = "XY",
    parameter FLIT_WIDTH     = DATA_WIDTH + VC_NUM + PRIO_WIDTH + PKT_ID_WIDTH + 1
)
(
    input  wire                         clk,
    input  wire                         rst_n,

    input  wire [DATA_WIDTH-1:0]        local_data_in,
    input  wire                         local_valid_in,
    output wire                         local_ready_out,

    input  wire [DATA_WIDTH-1:0]        ns_data_in,
    input  wire                         ns_valid_in,
    output wire                         ns_ready_out,

    input  wire [DATA_WIDTH-1:0]        ew_data_in,
    input  wire                         ew_valid_in,
    output wire                         ew_ready_out,

    input  wire [DATA_WIDTH-1:0]        fn_data_in,
    input  wire                         fn_valid_in,
    output wire                         fn_ready_out,

    output wire [DATA_WIDTH-1:0]        local_data_out,
    output wire                         local_valid_out,
    input  wire                         local_ready_in,

    output wire [DATA_WIDTH-1:0]        ns_data_out,
    output wire                         ns_valid_out,
    input  wire                         ns_ready_in,

    output wire [DATA_WIDTH-1:0]        ew_data_out,
    output wire                         ew_valid_out,
    input  wire                         ew_ready_in,

    output wire [DATA_WIDTH-1:0]        fn_data_out,
    output wire                         fn_valid_out,
    input  wire                         fn_ready_in,

    input  wire [PRIO_WIDTH-1:0]        qos_priority,
    output wire [7:0]                   congestion_status,
    output wire [NUM_PORTS-1:0]         vc_status
);

    localparam LOG2_PORTS = $clog2(NUM_PORTS);
    localparam LOG2_VC    = $clog2(VC_NUM);

    typedef struct packed {
        logic [DATA_WIDTH-1:0]     data;
        logic [VC_NUM-1:0]         vc_id;
        logic [PRIO_WIDTH-1:0]     prio;
        logic [PKT_ID_WIDTH-1:0]   pkt_id;
        logic                      valid;
    } flit_t;

    flit_t                             port_in  [0:NUM_PORTS-1];
    flit_t                             port_out [0:NUM_PORTS-1];
    wire                               port_ready_in  [0:NUM_PORTS-1];
    wire                               port_ready_out [0:NUM_PORTS-1];

    wire [LOG2_PORTS-1:0]              route_dest [0:NUM_PORTS-1];
    wire [NUM_PORTS-1:0]               route_valid [0:NUM_PORTS-1];

    wire [VC_NUM-1:0]                  vc_alloc_req  [0:NUM_PORTS-1];
    wire [VC_NUM-1:0]                  vc_alloc_grant [0:NUM_PORTS-1];

    reg  [7:0]                         cong_status_reg;
    integer i, j;

    assign {local_ready_out, ns_ready_out, ew_ready_out, fn_ready_out} = port_ready_out[0];
    assign port_ready_in[0] = local_ready_in;
    assign port_ready_in[1] = ns_ready_in;
    assign port_ready_in[2] = ew_ready_in;
    assign port_ready_in[3] = fn_ready_in;

    assign local_data_out = port_out[0].data;
    assign local_valid_out = port_out[0].valid;
    assign ns_data_out = port_out[1].data;
    assign ns_valid_out = port_out[1].valid;
    assign ew_data_out = port_out[2].data;
    assign ew_valid_out = port_out[2].valid;
    assign fn_data_out = port_out[3].data;
    assign fn_valid_out = port_out[3].valid;

    assign port_in[0] = '{data: local_data_in, vc_id: '0, prio: qos_priority, pkt_id: '0, valid: local_valid_in};
    assign port_in[1] = '{data: ns_data_in, vc_id: '0, prio: qos_priority, pkt_id: '0, valid: ns_valid_in};
    assign port_in[2] = '{data: ew_data_in, vc_id: '0, prio: qos_priority, pkt_id: '0, valid: ew_valid_in};
    assign port_in[3] = '{data: fn_data_in, vc_id: '0, prio: qos_priority, pkt_id: '0, valid: fn_valid_in};

    assign congestion_status = cong_status_reg;

    generate
        for (i = 0; i < NUM_PORTS; i = i + 1) begin : ROUTE_CALC
            route_compute #
            (
                .NUM_PORTS (NUM_PORTS),
                .ROUTE_TYPE (ROUTE_TYPE)
            )
            rc_inst
            (
                .dest_addr (port_in[i].data[15:0]),
                .src_port  (i[LOG2_PORTS-1:0]),
                .route_sel (route_dest[i]),
                .route_vld (route_valid[i])
            );
        end
    endgenerate

    generate
        for (i = 0; i < NUM_PORTS; i = i + 1) begin : VC_ALLOC
            vc_allocator #
            (
                .NUM_VC (VC_NUM)
            )
            vc_alloc_inst
            (
                .clk         (clk),
                .rst_n       (rst_n),
                .alloc_req   (vc_alloc_req[i]),
                .vc_id_in    (port_in[i].vc_id),
                .alloc_grant (vc_alloc_grant[i]),
                .vc_id_out   (port_out[i].vc_id)
            );
        end
    endgenerate

    generate
        for (i = 0; i < NUM_PORTS; i = i + 1) begin : INPUT_VC
            virtual_channel #
            (
                .VC_NUM        (VC_NUM),
                .VC_DEPTH      (VC_DEPTH),
                .DATA_WIDTH    (DATA_WIDTH + VC_NUM + PRIO_WIDTH + PKT_ID_WIDTH + 1),
                .PRIO_WIDTH    (0),
                .PKT_ID_WIDTH  (0)
            )
            vc_inst
            (
                .clk            (clk),
                .rst_n          (rst_n),

                .valid_in       (port_in[i].valid),
                .data_in        ({port_in[i].data, port_in[i].pkt_id, port_in[i].prio, port_in[i].vc_id}),
                .vc_id_in       ('0),
                .prio_in        (port_in[i].prio),
                .pkt_id_in      (port_in[i].pkt_id),

                .flit_out       (),
                .valid_out      (port_out[i].valid),
                .ready_in       (port_ready_in[i]),

                .credit_in      ('0),
                .credit_out     (),

                .vc_status      (vc_status[i])
            );

            always @(*) begin
                port_out[i].data = port_out[i].data;
                port_out[i].prio = port_in[i].prio;
                port_out[i].pkt_id = port_in[i].pkt_id;
            end
        end
    endgenerate

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            cong_status_reg <= 8'd0;
        end else begin
            cong_status_reg[7:4] <= {vc_status[0], vc_status[1], vc_status[2], vc_status[3]};
            cong_status_reg[3:0] <= 4'd0;
        end
    end

endmodule

module route_compute #
(
    parameter NUM_PORTS  = 5,
    parameter ROUTE_TYPE = "XY"
)
(
    input  wire [15:0]              dest_addr,
    input  wire [LOG2_PORTS-1:0]    src_port,
    output wire [LOG2_PORTS-1:0]    route_sel,
    output wire                     route_vld
);

    localparam LOG2_PORTS = $clog2(NUM_PORTS);

    generate
        if (ROUTE_TYPE == "XY") begin : XY_ROUTING
            always @(*) begin
                route_sel = src_port;
                route_vld = 1'b1;
                if (dest_addr[15:8] > 8'd127) begin
                    route_sel = 2'b01;
                end else if (dest_addr[15:8] < 8'd128) begin
                    route_sel = 2'b10;
                end else begin
                    route_sel = src_port;
                end
            end
        end else if (ROUTE_TYPE == "ADAPTIVE") begin : ADAPTIVE_ROUTING
            always @(*) begin
                route_sel = src_port;
                route_vld = 1'b1;
            end
        end else begin : DETERMINISTIC
            assign route_sel = src_port;
            assign route_vld = 1'b1;
        end
    endgenerate

endmodule

module vc_allocator #
(
    parameter NUM_VC = 4
)
(
    input  wire                     clk,
    input  wire                     rst_n,
    input  wire [NUM_VC-1:0]        alloc_req,
    input  wire [LOG2_VC-1:0]       vc_id_in,
    output wire [NUM_VC-1:0]        alloc_grant,
    output wire [LOG2_VC-1:0]       vc_id_out
);

    localparam LOG2_VC = $clog2(NUM_VC);

    reg  [LOG2_VC-1:0]              round_robin_ptr;
    reg  [NUM_VC-1:0]               alloc_grant_reg;
    wire [NUM_VC-1:0]               req_masked;
    wire [NUM_VC-1:0]               req_unmasked;
    wire [NUM_VC-1:0]               grant_masked;
    wire [NUM_VC-1:0]               grant_unmasked;

    assign req_unmasked = alloc_req;
    assign alloc_grant = grant_masked | grant_unmasked;

    fixed_prio_arbiter #
    (
        .NUM_PORTS (NUM_VC)
    )
    fpa
    (
        .req   (req_unmasked),
        .grant (grant_unmasked)
    );

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            round_robin_ptr <= {LOG2_VC{1'b0}};
            alloc_grant_reg <= {NUM_VC{1'b0}};
        end else begin
            if (grant_unmasked != {NUM_VC{1'b0}}) begin
                round_robin_ptr <= grant_unmasked[LOG2_VC-1:0];
            end
            alloc_grant_reg <= alloc_grant;
        end
    end

    assign vc_id_out = round_robin_ptr;

endmodule
