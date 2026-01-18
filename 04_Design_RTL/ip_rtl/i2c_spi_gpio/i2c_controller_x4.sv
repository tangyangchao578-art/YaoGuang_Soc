`timescale 1ns/1ps

module i2c_controller_x4 #
(
    parameter CHANNEL_ID = 0,
    parameter APB_DW = 32,
    parameter APB_AW = 12
)
(
    input  wire                    clk_apb,
    input  wire                    rst_apb_n,
    input  wire                    clk_i2c,
    input  wire                    rst_i2c_n,

    input  wire [APB_AW-1:0]       paddr,
    input  wire                    pwrite,
    input  wire [APB_DW-1:0]       pwdata,
    input  wire                    psel,
    input  wire                    penable,
    output reg  [APB_DW-1:0]       prdata,
    output reg                     pready,
    output reg                     pslverr,

    output wire                    i2c_scl,
    inout  wire                    i2c_sda,

    output wire [31:0]             int_raw,

    input  wire                    test_mode,
    input  wire                    scan_enable
);

    localparam REG_CTRL     = 'h00;
    localparam REG_STAT     = 'h04;
    localparam REG_SADDR    = 'h08;
    localparam REG_DATA     = 'h0C;
    localparam REG_INT_EN   = 'h10;
    localparam REG_INT_CLR  = 'h14;
    localparam REG_DIV      = 'h18;

    reg  [15:0]                    ctrl_reg;
    reg  [15:0]                    stat_reg;
    reg  [15:0]                    saddr_reg;
    reg  [7:0]                     data_reg;
    reg  [15:0]                    int_enable_reg;
    reg  [15:0]                    div_reg;

    wire                          apb_write;
    wire                          apb_read;

    wire                          scl_out;
    wire                          scl_oe;
    wire                          sda_out;
    wire                          sda_oe;
    wire                          sda_in;

    wire                          start_det;
    wire                          stop_det;
    wire                          addr_match;
    wire                          rx_ack;
    wire                          tx_done;
    wire                          rx_done;
    wire                          arb_lost;
    wire                          bus_busy;

    assign apb_write = psel && penable && pwrite;
    assign apb_read  = psel && penable && !pwrite;

    assign i2c_scl = scl_oe ? 1'b0 : 1'bz;
    assign i2c_sda = sda_oe ? sda_out : 1'bz;
    assign sda_in = i2c_sda;

    assign int_raw[31:8] = '0;
    assign int_raw[7] = stop_det;
    assign int_raw[6] = start_det;
    assign int_raw[5] = arb_lost;
    assign int_raw[4] = rx_ack;
    assign int_raw[3] = tx_done;
    assign int_raw[2] = rx_done;
    assign int_raw[1] = addr_match;
    assign int_raw[0] = bus_busy;

    always @(posedge clk_apb or negedge rst_apb_n) begin
        if (!rst_apb_n) begin
            ctrl_reg <= '0;
            saddr_reg <= '0;
            div_reg <= 'h0064;
            int_enable_reg <= '0;
        end else begin
            if (apb_write) begin
                case (paddr[3:0])
                    REG_CTRL: begin
                        ctrl_reg <= pwdata[15:0];
                    end
                    REG_SADDR: begin
                        saddr_reg <= pwdata[15:0];
                    end
                    REG_DIV: begin
                        div_reg <= pwdata[15:0];
                    end
                    REG_INT_EN: begin
                        int_enable_reg <= pwdata[15:0];
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
                case (paddr[3:0])
                    REG_CTRL: begin
                        prdata <= {16'h0, ctrl_reg};
                    end
                    REG_STAT: begin
                        prdata <= {16'h0, stat_reg};
                    end
                    REG_SADDR: begin
                        prdata <= {16'h0, saddr_reg};
                    end
                    REG_DATA: begin
                        prdata <= {24'h0, data_reg};
                    end
                    REG_INT_EN: begin
                        prdata <= {16'h0, int_enable_reg};
                    end
                    REG_DIV: begin
                        prdata <= {16'h0, div_reg};
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
            data_reg <= '0;
        end else begin
            stat_reg[0] <= bus_busy;
            stat_reg[1] <= addr_match;
            stat_reg[2] <= tx_done;
            stat_reg[3] <= rx_done;
            stat_reg[4] <= rx_ack;
            stat_reg[5] <= arb_lost;
            stat_reg[6] <= start_det;
            stat_reg[7] <= stop_det;

            if (apb_write && paddr[3:0] == REG_DATA) begin
                data_reg <= pwdata[7:0];
            end
        end
    end

    i2c_fsm #
    (
        .PRESCALE (100)
    ) u_i2c_fsm (
        .clk          (clk_i2c),
        .rst_n        (rst_i2c_n),
        .ctrl_reg     (ctrl_reg),
        .div_reg      (div_reg),
        .data_out     (data_reg),
        .data_in      (data_reg),
        .saddr        (saddr_reg[7:0]),
        .sda_in       (sda_in),
        .scl_out      (scl_out),
        .scl_oe       (scl_oe),
        .sda_out      (sda_out),
        .sda_oe       (sda_oe),
        .start_det    (start_det),
        .stop_det     (stop_det),
        .addr_match   (addr_match),
        .rx_ack       (rx_ack),
        .tx_done      (tx_done),
        .rx_done      (rx_done),
        .arb_lost     (arb_lost),
        .bus_busy     (bus_busy)
    );

endmodule

module i2c_fsm #
(
    parameter PRESCALE = 100
)
(
    input  wire                    clk,
    input  wire                    rst_n,
    input  wire [15:0]             ctrl_reg,
    input  wire [15:0]             div_reg,
    input  wire [7:0]              data_out,
    output reg  [7:0]              data_in,
    input  wire [7:0]              saddr,
    input  wire                    sda_in,
    output reg                     scl_out,
    output reg                     scl_oe,
    output reg                     sda_out,
    output reg                     sda_oe,
    output reg                     start_det,
    output reg                     stop_det,
    output reg                     addr_match,
    output reg                     rx_ack,
    output reg                     tx_done,
    output reg                     rx_done,
    output reg                     arb_lost,
    output reg                     bus_busy
);

    localparam IDLE       = 4'h0;
    localparam START      = 4'h1;
    localparam ADDR_SEND  = 4'h2;
    localparam ACK_WAIT   = 4'h3;
    localparam WRITE      = 4'h4;
    localparam READ       = 4'h5;
    localparam ACK_SEND   = 4'h6;
    localparam STOP       = 4'h7;

    reg  [3:0]                 state;
    reg  [3:0]                 bit_counter;
    reg  [7:0]                 shift_reg;
    reg                        master_mode;
    reg                        tx_mode;
    reg                        scl_high_wait;
    reg  [15:0]                prescale_cnt;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            bus_busy <= 1'b0;
            start_det <= 1'b0;
            stop_det <= 1'b0;
            addr_match <= 1'b0;
            tx_done <= 1'b0;
            rx_done <= 1'b0;
            rx_ack <= 1'b0;
            arb_lost <= 1'b0;
            data_in <= '0;
        end else begin
            start_det <= 1'b0;
            stop_det <= 1'b0;
            tx_done <= 1'b0;
            rx_done <= 1'b0;
            rx_ack <= 1'b0;
            arb_lost <= 1'b0;

            case (state)
                IDLE: begin
                    scl_oe <= 1'b0;
                    sda_oe <= 1'b0;
                    if (ctrl_reg[0] && !sda_in && scl_in) begin
                        state <= START;
                        bus_busy <= 1'b1;
                        start_det <= 1'b1;
                    end
                end
                START: begin
                    sda_oe <= 1'b1;
                    sda_out <= 1'b0;
                    state <= ADDR_SEND;
                    bit_counter <= 7;
                    shift_reg <= saddr;
                    master_mode <= ctrl_reg[1];
                    tx_mode <= ctrl_reg[2];
                end
                ADDR_SEND: begin
                    scl_oe <= 1'b1;
                    scl_out <= 1'b0;
                    if (bit_counter > 0) begin
                        bit_counter <= bit_counter - 1;
                        scl_out <= shift_reg[bit_counter];
                        shift_reg[bit_counter] <= sda_in;
                    end else begin
                        state <= ACK_WAIT;
                    end
                end
                ACK_WAIT: begin
                    scl_oe <= 1'b1;
                    scl_out <= 1'b1;
                    if (sda_in) begin
                        if (master_mode) begin
                            arb_lost <= 1'b1;
                            state <= IDLE;
                            bus_busy <= 1'b0;
                        end
                    end else begin
                        addr_match <= 1'b1;
                        if (tx_mode) begin
                            state <= WRITE;
                            shift_reg <= data_out;
                            bit_counter <= 7;
                        end else begin
                            state <= READ;
                            bit_counter <= 7;
                        end
                    end
                end
                WRITE: begin
                    scl_oe <= 1'b1;
                    scl_out <= 1'b0;
                    if (bit_counter > 0) begin
                        bit_counter <= bit_counter - 1;
                        scl_out <= shift_reg[bit_counter];
                    end else begin
                        state <= ACK_WAIT;
                        rx_ack <= sda_in;
                        if (sda_in) begin
                            tx_done <= 1'b1;
                            state <= STOP;
                        end
                    end
                end
                READ: begin
                    scl_oe <= 1'b1;
                    scl_out <= 1'b1;
                    if (bit_counter > 0) begin
                        bit_counter <= bit_counter - 1;
                        data_in[7-bit_counter] <= sda_in;
                    end else begin
                        rx_done <= 1'b1;
                        state <= ACK_SEND;
                    end
                end
                ACK_SEND: begin
                    sda_oe <= 1'b1;
                    sda_out <= 1'b0;
                    scl_oe <= 1'b1;
                    scl_out <= 1'b1;
                    state <= STOP;
                end
                STOP: begin
                    sda_oe <= 1'b1;
                    sda_out <= 1'b0;
                    scl_oe <= 1'b0;
                    state <= IDLE;
                    bus_busy <= 1'b0;
                    stop_det <= 1'b1;
                end
            endcase
        end
    end

    wire scl_in;
    assign scl_in = 1'b1;

endmodule
