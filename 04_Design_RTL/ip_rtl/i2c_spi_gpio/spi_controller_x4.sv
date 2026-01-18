`timescale 1ns/1ps

module spi_controller_x4 #
(
    parameter CHANNEL_ID = 0,
    parameter APB_DW = 32,
    parameter APB_AW = 12
)
(
    input  wire                    clk_apb,
    input  wire                    rst_apb_n,
    input  wire                    clk_spi,
    input  wire                    rst_spi_n,

    input  wire [APB_AW-1:0]       paddr,
    input  wire                    pwrite,
    input  wire [APB_DW-1:0]       pwdata,
    input  wire                    psel,
    input  wire                    penable,
    output reg  [APB_DW-1:0]       prdata,
    output reg                     pready,
    output reg                     pslverr,

    output wire                    spi_sck,
    output wire [3:0]              spi_cs,
    output wire [3:0]              spi_mosi,
    input  wire [3:0]              spi_miso,

    output wire [31:0]             int_raw,

    input  wire                    test_mode,
    input  wire                    scan_enable
);

    localparam REG_CTRL     = 'h00;
    localparam REG_STAT     = 'h04;
    localparam REG_DATA     = 'h08;
    localparam REG_CS       = 'h0C;
    localparam REG_BAUD     = 'h10;
    localparam REG_INT_EN   = 'h14;
    localparam REG_INT_CLR  = 'h18;

    reg  [15:0]                    ctrl_reg;
    reg  [15:0]                    stat_reg;
    reg  [15:0]                    data_reg;
    reg  [15:0]                    cs_reg;
    reg  [7:0]                     baud_reg;
    reg  [15:0]                    int_enable_reg;

    wire                          apb_write;
    wire                          apb_read;

    wire                          tx_empty;
    wire                          rx_full;
    wire                          tx_overflow;
    wire                          rx_underflow;
    wire                          mode_fault;

    assign apb_write = psel && penable && pwrite;
    assign apb_read  = psel && penable && !pwrite;

    assign int_raw[31:6] = '0;
    assign int_raw[5] = mode_fault;
    assign int_raw[4] = rx_underflow;
    assign int_raw[3] = tx_overflow;
    assign int_raw[2] = rx_full;
    assign int_raw[1] = tx_empty;
    assign int_raw[0] = spi_done;

    assign spi_sck = 1'b0;
    assign spi_cs = 4'hF;
    assign spi_mosi = 4'h0;

    always @(posedge clk_apb or negedge rst_apb_n) begin
        if (!rst_apb_n) begin
            ctrl_reg <= '0;
            cs_reg <= 'hFFFF;
            baud_reg <= 'h0A;
            int_enable_reg <= '0;
        end else begin
            if (apb_write) begin
                case (paddr[3:0])
                    REG_CTRL: begin
                        ctrl_reg <= pwdata[15:0];
                    end
                    REG_CS: begin
                        cs_reg <= pwdata[15:0];
                    end
                    REG_BAUD: begin
                        baud_reg <= pwdata[7:0];
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
                    REG_DATA: begin
                        prdata <= {16'h0, data_reg};
                    end
                    REG_CS: begin
                        prdata <= {16'h0, cs_reg};
                    end
                    REG_BAUD: begin
                        prdata <= {24'h0, baud_reg};
                    end
                    REG_INT_EN: begin
                        prdata <= {16'h0, int_enable_reg};
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
            if (apb_write && paddr[3:0] == REG_DATA) begin
                data_reg <= pwdata[15:0];
            end

            stat_reg[0] <= tx_empty;
            stat_reg[1] <= rx_full;
            stat_reg[2] <= tx_overflow;
            stat_reg[3] <= rx_underflow;
            stat_reg[4] <= mode_fault;
            stat_reg[5] <= spi_done;
        end
    end

    wire spi_done;
    assign spi_done = 1'b0;

    spi_fsm #
    (
        .DATA_WIDTH (16)
    ) u_spi_fsm (
        .clk          (clk_spi),
        .rst_n        (rst_spi_n),
        .ctrl_reg     (ctrl_reg),
        .baud_reg     (baud_reg),
        .data_out     (data_reg),
        .data_in      (data_reg),
        .cs_reg       (cs_reg),
        .mosi         (spi_mosi),
        .miso         (spi_miso),
        .sck          (spi_sck),
        .cs           (spi_cs),
        .tx_empty     (tx_empty),
        .rx_full      (rx_full),
        .tx_overflow  (tx_overflow),
        .rx_underflow (rx_underflow),
        .mode_fault   (mode_fault),
        .done         (spi_done)
    );

endmodule

module spi_fsm #
(
    parameter DATA_WIDTH = 16
)
(
    input  wire                    clk,
    input  wire                    rst_n,
    input  wire [15:0]             ctrl_reg,
    input  wire [7:0]              baud_reg,
    input  wire [DATA_WIDTH-1:0]   data_out,
    output reg  [DATA_WIDTH-1:0]   data_in,
    input  wire [15:0]             cs_reg,
    output wire [3:0]              mosi,
    input  wire [3:0]              miso,
    output wire                    sck,
    output wire [3:0]              cs,
    output reg                     tx_empty,
    output reg                     rx_full,
    output reg                     tx_overflow,
    output reg                     rx_underflow,
    output reg                     mode_fault,
    output reg                     done
);

    localparam IDLE       = 3'h0;
    localparam TRANSFER   = 3'h1;
    localparam WAIT       = 3'h2;

    reg  [2:0]                 state;
    reg  [4:0]                 bit_counter;
    reg  [DATA_WIDTH-1:0]      tx_shift;
    reg  [DATA_WIDTH-1:0]      rx_shift;
    reg                        cpol;
    reg                        cpha;
    reg                        msb_first;
    reg  [7:0]                 baud_counter;
    reg                        sck_reg;
    reg                        cs_active;
    reg  [3:0]                 cs_reg_sync;

    assign mosi[0] = tx_shift[DATA_WIDTH-1];
    assign mosi[1] = tx_shift[DATA_WIDTH-1];
    assign mosi[2] = tx_shift[DATA_WIDTH-1];
    assign mosi[3] = tx_shift[DATA_WIDTH-1];
    assign sck = sck_reg;
    assign cs = cs_active ? cs_reg_sync : 4'hF;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            done <= 1'b0;
            tx_empty <= 1'b1;
            rx_full <= 1'b0;
            tx_overflow <= 1'b0;
            rx_underflow <= 1'b0;
            mode_fault <= 1'b0;
            data_in <= '0;
            tx_shift <= '0;
            rx_shift <= '0;
            bit_counter <= DATA_WIDTH - 1;
            sck_reg <= 1'b0;
            cs_active <= 1'b0;
            cs_reg_sync <= 4'hF;
        end else begin
            tx_overflow <= 1'b0;
            rx_underflow <= 1'b0;
            done <= 1'b0;

            case (state)
                IDLE: begin
                    sck_reg <= cpol;
                    cs_active <= 1'b0;
                    if (ctrl_reg[0]) begin
                        cpol <= ctrl_reg[1];
                        cpha <= ctrl_reg[2];
                        msb_first <= ctrl_reg[3];
                        cs_reg_sync <= cs_reg[3:0];
                        state <= TRANSFER;
                        bit_counter <= DATA_WIDTH - 1;
                        tx_shift <= data_out;
                        rx_shift <= '0;
                        cs_active <= 1'b1;
                    end else begin
                        tx_empty <= 1'b1;
                    end
                end
                TRANSFER: begin
                    if (baud_counter == 0) begin
                        baud_counter <= baud_reg;
                        sck_reg <= ~sck_reg;
                        if (sck_reg == cpha) begin
                            if (msb_first) begin
                                rx_shift <= {rx_shift[DATA_WIDTH-2:0], miso[0]};
                            end else begin
                                rx_shift <= {miso[0], rx_shift[DATA_WIDTH-1:1]};
                            end
                            if (bit_counter > 0) begin
                                bit_counter <= bit_counter - 1;
                                if (msb_first) begin
                                    tx_shift <= {tx_shift[DATA_WIDTH-2:0], 1'b0};
                                end else begin
                                    tx_shift <= {1'b0, tx_shift[DATA_WIDTH-1:1]};
                                end
                            end else begin
                                state <= WAIT;
                                done <= 1'b1;
                                data_in <= rx_shift;
                                rx_full <= 1'b1;
                                cs_active <= 1'b0;
                            end
                        end else begin
                            if (msb_first) begin
                                rx_shift <= {rx_shift[DATA_WIDTH-2:0], miso[0]};
                            end else begin
                                rx_shift <= {miso[0], rx_shift[DATA_WIDTH-1:1]};
                            end
                        end
                    end else begin
                        baud_counter <= baud_counter - 1;
                    end
                end
                WAIT: begin
                    if (!ctrl_reg[0]) begin
                        state <= IDLE;
                        rx_full <= 1'b0;
                        tx_empty <= 1'b1;
                    end
                end
            endcase
        end
    end

endmodule
