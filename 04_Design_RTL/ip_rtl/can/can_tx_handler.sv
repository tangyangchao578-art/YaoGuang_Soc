`timescale 1ns/1ps

module can_tx_handler #
(
    parameter FIFO_DEPTH = 32,
    parameter DATA_WIDTH = 64,
    parameter ID_WIDTH = 32
)
(
    input  wire                    clk_can,
    input  wire                    rst_n,
    input  wire [ID_WIDTH-1:0]     tx_id,
    input  wire [DATA_WIDTH-1:0]   tx_data,
    input  wire                    tx_req,
    output reg                     tx_done,
    input  wire                    tx_cancel,
    output wire                    tx_empty,
    output wire                    can_tx,
    input  wire [15:0]             bit_time,
    output reg                     arb_lost,
    output reg                     active_err
);

    localparam IDLE       = 4'h0;
    localparam ARBITRATION = 4'h1;
    localparam SEND_SOF   = 4'h2;
    localparam SEND_ID    = 4'h3;
    localparam SEND_RTR   = 4'h4;
    localparam SEND_IDE   = 4'h5;
    localparam SEND_DLC   = 4'h6;
    localparam SEND_DATA  = 4'h7;
    localparam SEND_CRC   = 4'h8;
    localparam SEND_CRC_DEL = 4'h9;
    localparam SEND_ACK   = 4'hA;
    localparam SEND_ACK_DEL = 4'hB;
    localparam SEND_EOF   = 4'hC;
    localparam WAIT       = 4'hD;
    localparam ERROR      = 4'hE;
    localparam OVERLOAD   = 4'hF;

    reg  [3:0]                 state;
    reg  [3:0]                 next_state;
    reg  [5:0]                 bit_counter;
    reg  [5:0]                 bit_len;
    reg  [63:0]                tx_data_reg;
    reg  [31:0]                tx_id_reg;
    reg  [4:0]                 dlc;
    reg                        tx_data_filled;
    reg                        sending;
    reg                        bit_stuff;
    reg  [5:0]                 stuff_count;
    reg                        tx_bit;
    reg                        tx_dominant;
    reg                        rx_bit;
    reg                        rx_dominant;
    reg                        ack_received;

    wire                       arbitration_lost;
    wire                       error_flag_active;
    wire                       stuff_bit;
    wire                       dominant_bit;
    wire                       recessive_bit;

    assign tx_empty = !sending && !tx_data_filled;
    assign dominant_bit = 1'b0;
    assign recessive_bit = 1'b1;
    assign arbitration_lost = tx_dominant && rx_dominant;
    assign stuff_bit = stuff_count == 5;
    assign can_tx = tx_dominant ? dominant_bit : recessive_bit;

    always @(posedge clk_can or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            tx_done <= 1'b0;
            arb_lost <= 1'b0;
            active_err <= 1'b0;
            sending <= 1'b0;
            tx_data_filled <= 1'b0;
        end else begin
            tx_done <= 1'b0;
            arb_lost <= 1'b0;
            active_err <= 1'b0;

            case (state)
                IDLE: begin
                    if (tx_req) begin
                        tx_id_reg <= tx_id;
                        tx_data_reg <= tx_data;
                        tx_data_filled <= 1'b1;
                        sending <= 1'b1;
                        state <= SEND_SOF;
                    end
                end
                SEND_SOF: begin
                    if (bit_counter == 0) begin
                        state <= ARBITRATION;
                        bit_counter <= 11;
                    end
                end
                ARBITRATION: begin
                    if (arbitration_lost) begin
                        state <= IDLE;
                        sending <= 1'b0;
                        arb_lost <= 1'b1;
                    end else if (bit_counter == 0) begin
                        state <= SEND_IDE;
                    end
                end
                SEND_IDE: begin
                    if (bit_counter == 0) begin
                        state <= SEND_DLC;
                        bit_counter <= 3;
                    end
                end
                SEND_DLC: begin
                    if (bit_counter == 0) begin
                        dlc <= tx_id_reg[3:0];
                        state <= SEND_DATA;
                        bit_counter <= dlc * 8 - 1;
                    end
                end
                SEND_DATA: begin
                    if (bit_counter == 0) begin
                        state <= SEND_CRC;
                        bit_counter <= 15;
                    end
                end
                SEND_CRC: begin
                    if (bit_counter == 0) begin
                        state <= SEND_CRC_DEL;
                        bit_counter <= 1;
                    end
                end
                SEND_CRC_DEL: begin
                    if (bit_counter == 0) begin
                        state <= SEND_ACK;
                    end
                end
                SEND_ACK: begin
                    if (bit_counter == 0) begin
                        state <= SEND_ACK_DEL;
                    end
                end
                SEND_ACK_DEL: begin
                    if (bit_counter == 0) begin
                        state <= SEND_EOF;
                        bit_counter <= 6;
                    end
                end
                SEND_EOF: begin
                    if (bit_counter == 0) begin
                        state <= IDLE;
                        sending <= 1'b0;
                        tx_data_filled <= 1'b0;
                        tx_done <= 1'b1;
                    end
                end
                ERROR: begin
                    state <= IDLE;
                    sending <= 1'b0;
                    active_err <= 1'b1;
                end
            endcase
        end
    end

    always @(posedge clk_can or negedge rst_n) begin
        if (!rst_n) begin
            bit_counter <= '0;
            stuff_count <= '0;
            tx_dominant <= 1'b0;
        end else begin
            case (state)
                SEND_SOF,
                ARBITRATION,
                SEND_IDE,
                SEND_DLC,
                SEND_DATA,
                SEND_CRC,
                SEND_CRC_DEL,
                SEND_ACK,
                SEND_ACK_DEL,
                SEND_EOF: begin
                    if (bit_counter > 0) begin
                        bit_counter <= bit_counter - 1;
                    end

                    if (tx_dominant) begin
                        if (tx_bit == dominant_bit) begin
                            stuff_count <= stuff_count + 1;
                        end else begin
                            stuff_count <= '0;
                        end
                    end
                end
                default: begin
                    bit_counter <= '0;
                    stuff_count <= '0;
                end
            endcase
        end
    end

    always @(*) begin
        tx_bit = recessive_bit;
        tx_dominant = 1'b0;

        case (state)
            SEND_SOF: begin
                tx_bit = dominant_bit;
                tx_dominant = 1'b1;
            end
            ARBITRATION: begin
                if (bit_counter < 10) begin
                    tx_bit = tx_id_reg[10-bit_counter];
                    tx_dominant = (tx_bit == dominant_bit);
                end else if (bit_counter == 10) begin
                    tx_bit = recessive_bit;
                    tx_dominant = 1'b0;
                end
            end
            SEND_IDE: begin
                tx_bit = recessive_bit;
                tx_dominant = 1'b0;
            end
            SEND_DLC: begin
                tx_bit = dlc[4-bit_counter];
                tx_dominant = (tx_bit == dominant_bit);
            end
            SEND_DATA: begin
                if (bit_counter < 32) begin
                    tx_bit = tx_data_reg[31-bit_counter];
                    tx_dominant = (tx_bit == dominant_bit);
                end else begin
                    tx_bit = tx_data_reg[63-(bit_counter-32)];
                    tx_dominant = (tx_bit == dominant_bit);
                end
            end
            SEND_CRC: begin
                tx_bit = recessive_bit;
                tx_dominant = 1'b0;
            end
            SEND_ACK,
            SEND_ACK_DEL: begin
                tx_bit = recessive_bit;
                tx_dominant = 1'b0;
            end
            SEND_EOF: begin
                tx_bit = recessive_bit;
                tx_dominant = 1'b0;
            end
        endcase
    end

endmodule
