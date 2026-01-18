`timescale 1ns/1ps

module can_top #
(
    parameter CHANNELS = 4,
    parameter APB_DW = 32,
    parameter APB_AW = 12
)
(
    input  wire                    clk_apb,
    input  wire                    rst_apb_n,
    input  wire                    clk_can,
    input  wire                    rst_can_n,
    input  wire                    clk_ref,
    input  wire                    rst_ref_n,

    input  wire [APB_AW-1:0]       paddr,
    input  wire                    pwrite,
    input  wire [APB_DW-1:0]       pwdata,
    input  wire                    psel,
    input  wire                    penable,
    output reg  [APB_DW-1:0]       prdata,
    output reg                     pready,
    output reg                     pslverr,

    output wire [CHANNELS-1:0]     can_tx,
    input  wire [CHANNELS-1:0]     can_rx,
    output wire [CHANNELS-1:0]     can_en,
    output wire [CHANNELS-1:0]     can_stdby,

    output wire [5:0]              int_tx_done,
    output wire [5:0]              int_rx_done,
    output wire [5:0]              int_error,
    output wire [5:0]              int_wakeup,
    output wire                    int_global,

    input  wire                    test_mode,
    input  wire                    scan_enable
);

    localparam CHAN_CTRL_OFFSET = 'h100;
    localparam CHAN_CTRL_SIZE   = 'h100;

    wire [31:0]                   ctrl_reg;
    wire [31:0]                   stat_reg;
    wire [31:0]                   err_tx_reg;
    wire [31:0]                   err_rx_reg;
    wire [31:0]                   btr_reg;
    wire [31:0]                   int_enable_reg;
    wire [31:0]                   int_stat_reg;
    wire [31:0]                   version_reg;

    genvar                         i;
    generate
        for (i = 0; i < CHANNELS; i = i + 1) begin : CHANNEL
            wire [31:0]           tx_id;
            wire [63:0]           tx_data;
            wire                  tx_req;
            wire                  tx_done;
            wire                  tx_cancel;
            wire                  tx_empty;

            wire [31:0]           rx_id;
            wire [63:0]           rx_data;
            wire                  rx_ready;
            wire                  rx_ack;
            wire                  rx_overflow;

            wire                  error_warning;
            wire                  error_passive;
            wire                  bus_off;
            wire                  arb_lost;
            wire                  active_err;

            can_controller #
            (
                .APB_DW (APB_DW),
                .APB_AW (APB_AW)
            ) u_can_controller (
                .clk_apb      (clk_apb),
                .rst_apb_n    (rst_apb_n),
                .clk_can      (clk_can),
                .rst_can_n    (rst_can_n),
                .clk_ref      (clk_ref),
                .rst_ref_n    (rst_ref_n),

                .paddr        (paddr),
                .pwrite       (pwrite),
                .pwdata       (pwdata),
                .psel         (psel && (paddr[11:8] == i)),
                .penable      (penable),
                .prdata       (prdata),
                .pready       (pready),
                .pslverr      (pslverr),

                .can_tx       (can_tx[i]),
                .can_rx       (can_rx[i]),
                .can_en       (can_en[i]),
                .can_stdby    (can_stdby[i]),

                .tx_id        (tx_id),
                .tx_data      (tx_data),
                .tx_req       (tx_req),
                .tx_done      (tx_done),
                .tx_cancel    (tx_cancel),
                .tx_empty     (tx_empty),

                .rx_id        (rx_id),
                .rx_data      (rx_data),
                .rx_ready     (rx_ready),
                .rx_ack       (rx_ack),
                .rx_overflow  (rx_overflow),

                .error_warning(error_warning),
                .error_passive(error_passive),
                .bus_off      (bus_off),
                .arb_lost     (arb_lost),
                .active_err   (active_err),

                .int_tx_done  (int_tx_done[i]),
                .int_rx_done  (int_rx_done[i]),
                .int_error    (int_error[i]),
                .int_wakeup   (int_wakeup[i]),

                .test_mode    (test_mode),
                .scan_enable  (scan_enable)
            );
        end
    endgenerate

    assign int_global = |int_stat_reg[CHANNELS*4-1:0];

    assign version_reg = {
        8'h01,
        8'h00,
        8'h00,
        8'h00
    };

endmodule
