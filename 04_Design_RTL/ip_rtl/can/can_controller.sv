`timescale 1ns/1ps

module can_controller #
(
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

    output wire                    can_tx,
    input  wire                    can_rx,
    output wire                    can_en,
    output wire                    can_stdby,

    output wire [31:0]             tx_id,
    output wire [63:0]             tx_data,
    output wire                    tx_req,
    input  wire                    tx_done,
    output wire                    tx_cancel,
    input  wire                    tx_empty,

    input  wire [31:0]             rx_id,
    input  wire [63:0]             rx_data,
    input  wire                    rx_ready,
    output wire                    rx_ack,
    input  wire                    rx_overflow,

    input  wire                    error_warning,
    input  wire                    error_passive,
    input  wire                    bus_off,
    input  wire                    arb_lost,
    input  wire                    active_err,

    output wire                    int_tx_done,
    output wire                    int_rx_done,
    output wire                    int_error,
    output wire                    int_wakeup,

    input  wire                    test_mode,
    input  wire                    scan_enable
);

    localparam REG_CTRL     = 'h000;
    localparam REG_STAT     = 'h004;
    localparam REG_ERR_TX   = 'h008;
    localparam REG_ERR_RX   = 'h00C;
    localparam REG_BTR      = 'h010;
    localparam REG_INT_EN   = 'h014;
    localparam REG_INT_STAT = 'h018;
    localparam REG_INT_CLR  = 'h01C;
    localparam REG_TX_ID    = 'h020;
    localparam REG_TX_DATA0 = 'h024;
    localparam REG_TX_DATA1 = 'h028;
    localparam REG_TX_CTRL  = 'h030;
    localparam REG_RX_ID    = 'h040;
    localparam REG_RX_DATA0 = 'h044;
    localparam REG_RX_DATA1 = 'h048;
    localparam REG_RX_CTRL  = 'h050;
    localparam REG_AF_CTRL  = 'h060;
    localparam REG_VERSION  = 'h3F0;

    reg  [31:0]                  ctrl_reg;
    reg  [31:0]                  stat_reg;
    reg  [31:0]                  err_tx_reg;
    reg  [31:0]                  err_rx_reg;
    reg  [31:0]                  btr_reg;
    reg  [31:0]                  int_enable_reg;
    reg  [31:0]                  int_stat_reg;
    reg  [31:0]                  tx_id_reg;
    reg  [63:0]                  tx_data_reg;
    reg  [31:0]                  tx_ctrl_reg;
    reg  [31:0]                  rx_id_reg;
    reg  [63:0]                  rx_data_reg;
    reg  [31:0]                  rx_ctrl_reg;
    reg  [31:0]                  af_ctrl_reg;
    reg  [7:0]                   version_reg;

    wire                         apb_write;
    wire                         apb_read;
    reg                          apb_ready_reg;

    assign apb_write = psel && penable && pwrite;
    assign apb_read  = psel && penable && !pwrite;

    always @(posedge clk_apb or negedge rst_apb_n) begin
        if (!rst_apb_n) begin
            ctrl_reg       <= '0;
            btr_reg        <= 'h001F000A;
            int_enable_reg <= '0;
            tx_ctrl_reg    <= '0;
            rx_ctrl_reg    <= '0;
            af_ctrl_reg    <= '0;
        end else begin
            if (apb_write) begin
                case (paddr[9:0])
                    REG_CTRL: begin
                        ctrl_reg <= pwdata;
                    end
                    REG_BTR: begin
                        btr_reg <= pwdata;
                    end
                    REG_INT_EN: begin
                        int_enable_reg <= pwdata;
                    end
                    REG_TX_CTRL: begin
                        tx_ctrl_reg <= pwdata;
                    end
                    REG_RX_CTRL: begin
                        rx_ctrl_reg <= pwdata;
                    end
                    REG_AF_CTRL: begin
                        af_ctrl_reg <= pwdata;
                    end
                endcase
            end
        end
    end

    always @(posedge clk_apb or negedge rst_apb_n) begin
        if (!rst_apb_n) begin
            tx_id_reg  <= '0;
            tx_data_reg <= '0;
        end else begin
            if (apb_write) begin
                case (paddr[9:0])
                    REG_TX_ID: begin
                        tx_id_reg <= pwdata;
                    end
                    REG_TX_DATA0: begin
                        tx_data_reg[31:0] <= pwdata;
                    end
                    REG_TX_DATA1: begin
                        tx_data_reg[63:32] <= pwdata;
                    end
                endcase
            end
        end
    end

    always @(posedge clk_apb or negedge rst_apb_n) begin
        if (!rst_apb_n) begin
            prdata <= '0;
            pready <= 1'b0;
            pslverr <= 1'b0;
        end else begin
            pready <= 1'b0;
            pslverr <= 1'b0;

            if (apb_read) begin
                pready <= 1'b1;
                case (paddr[9:0])
                    REG_CTRL: begin
                        prdata <= ctrl_reg;
                    end
                    REG_STAT: begin
                        prdata <= stat_reg;
                    end
                    REG_ERR_TX: begin
                        prdata <= err_tx_reg;
                    end
                    REG_ERR_RX: begin
                        prdata <= err_rx_reg;
                    end
                    REG_BTR: begin
                        prdata <= btr_reg;
                    end
                    REG_INT_EN: begin
                        prdata <= int_enable_reg;
                    end
                    REG_INT_STAT: begin
                        prdata <= int_stat_reg;
                    end
                    REG_TX_ID: begin
                        prdata <= tx_id_reg;
                    end
                    REG_TX_DATA0: begin
                        prdata <= tx_data_reg[31:0];
                    end
                    REG_TX_DATA1: begin
                        prdata <= tx_data_reg[63:32];
                    end
                    REG_TX_CTRL: begin
                        prdata <= tx_ctrl_reg;
                    end
                    REG_RX_ID: begin
                        prdata <= rx_id_reg;
                    end
                    REG_RX_DATA0: begin
                        prdata <= rx_data_reg[31:0];
                    end
                    REG_RX_DATA1: begin
                        prdata <= rx_data_reg[63:32];
                    end
                    REG_RX_CTRL: begin
                        prdata <= rx_ctrl_reg;
                    end
                    REG_AF_CTRL: begin
                        prdata <= af_ctrl_reg;
                    end
                    REG_VERSION: begin
                        prdata <= {24'h0, version_reg};
                    end
                    default: begin
                        prdata <= '0;
                        pslverr <= 1'b1;
                    end
                endcase
            end
        end
    end

    always @(posedge clk_apb or negedge rst_apb_n) begin
        if (!rst_apb_n) begin
            stat_reg <= '0;
            err_tx_reg <= '0;
            err_rx_reg <= '0;
            rx_id_reg <= '0;
            rx_data_reg <= '0;
            int_stat_reg <= '0;
        end else begin
            stat_reg <= {
                22'h0,
                bus_off,
                error_passive,
                error_warning,
                3'h0,
                active_err,
                arb_lost,
                rx_overflow,
                1'b0,
                tx_empty
            };

            if (tx_done) begin
                int_stat_reg[0] <= 1'b1;
            end

            if (rx_ready) begin
                rx_id_reg <= rx_id;
                rx_data_reg <= rx_data;
                int_stat_reg[1] <= 1'b1;
            end

            if (error_warning || error_passive || bus_off) begin
                int_stat_reg[2] <= 1'b1;
            end
        end
    end

    assign can_tx = 1'b1;
    assign can_en = ctrl_reg[0];
    assign can_stdby = ctrl_reg[1];

    assign tx_id = tx_id_reg;
    assign tx_data = tx_data_reg;
    assign tx_req = tx_ctrl_reg[0];
    assign tx_cancel = tx_ctrl_reg[1];
    assign rx_ack = rx_ctrl_reg[0];

    assign int_tx_done = int_stat_reg[0] & int_enable_reg[0];
    assign int_rx_done = int_stat_reg[1] & int_enable_reg[1];
    assign int_error   = int_stat_reg[2] & int_enable_reg[2];
    assign int_wakeup  = int_stat_reg[3] & int_enable_reg[3];

    can_bit_timing #
    (
        .TQ_DIVISOR (8)
    ) u_bit_timing (
        .clk_ref      (clk_ref),
        .rst_n        (rst_ref_n),
        .btr_config   (btr_reg),
        .bit_time     (),
        .sync_seg     (),
        .prop_seg     (),
        .phase_seg1   (),
        .phase_seg2   ()
    );

    can_tx_handler #
    (
        .FIFO_DEPTH (32)
    ) u_tx_handler (
        .clk_can     (clk_can),
        .rst_n       (rst_can_n),
        .tx_id       (tx_id),
        .tx_data     (tx_data),
        .tx_req      (tx_req),
        .tx_done     (tx_done),
        .tx_cancel   (tx_cancel),
        .tx_empty    (tx_empty),
        .can_tx      (can_tx),
        .bit_time    (),
        .arb_lost    (arb_lost),
        .active_err  (active_err)
    );

    can_rx_handler #
    (
        .FIFO_DEPTH (64)
    ) u_rx_handler (
        .clk_can     (clk_can),
        .rst_n       (rst_can_n),
        .can_rx      (can_rx),
        .rx_id       (rx_id),
        .rx_data     (rx_data),
        .rx_ready    (rx_ready),
        .rx_ack      (rx_ack),
        .rx_overflow (rx_overflow),
        .bit_time    (),
        .error_frame ()
    );

    can_error_handler #
    (
        .TX_ERR_LIMIT (255),
        .RX_ERR_LIMIT (255)
    ) u_error_handler (
        .clk_can       (clk_can),
        .rst_n         (rst_can_n),
        .can_rx        (can_rx),
        .tx_done       (tx_done),
        .rx_ready      (rx_ready),
        .crc_error     (),
        .form_error    (),
        .bit_error     (),
        .ack_error     (),
        .err_tx_count  (err_tx_reg),
        .err_rx_count  (err_rx_reg),
        .error_warning (error_warning),
        .error_passive (error_passive),
        .bus_off       (bus_off),
        .active_err    (active_err)
    );

endmodule
