`timescale 1ns/1ps

module can_rx_handler #
(
    parameter FIFO_DEPTH = 64,
    parameter DATA_WIDTH = 64,
    parameter ID_WIDTH = 32
)
(
    input  wire                    clk_can,
    input  wire                    rst_n,
    input  wire                    can_rx,
    output reg  [ID_WIDTH-1:0]     rx_id,
    output reg  [DATA_WIDTH-1:0]   rx_data,
    output reg                     rx_ready,
    input  wire                    rx_ack,
    output reg                     rx_overflow,
    input  wire [15:0]             bit_time,
    output reg                     error_frame
);

    localparam IDLE       = 4'h0;
    localparam RECEIVE    = 4'h1;
    localparam CHECK_ID   = 4'h2;
    localparam CHECK_DLC  = 4'h3;
    localparam DATA_PHASE = 4'h4;
    localparam CHECK_CRC  = 4'h5;
    localparam ACK_SLOT   = 4'h6;
    localparam END_OF_FR  = 4'h7;
    localparam ERROR_FR   = 4'h8;
    localparam OVERLOAD   = 4'h9;

    reg  [3:0]                 state;
    reg  [3:0]                 next_state;
    reg  [5:0]                 bit_counter;
    reg  [31:0]                rx_id_reg;
    reg  [63:0]                rx_data_reg;
    reg  [4:0]                 dlc_reg;
    reg  [14:0]                crc_reg;
    reg                        rtr_bit;
    reg                        ide_bit;
    reg                        fdf_bit;
    reg                        rx_dominant;
    reg                        rx_bit;
    reg                        bit_stuff;
    reg  [5:0]                 stuff_count;
    reg  [3:0]                 crc_counter;
    reg                        crc_error;
    reg                        form_error;
    reg                        crc_match;
    reg  [FIFO_DEPTH-1:0]      rx_fifo_wr_ptr;
    reg  [FIFO_DEPTH-1:0]      rx_fifo_rd_ptr;
    reg                        rx_fifo_full;
    reg                        rx_fifo_empty;
    reg  [FIFO_DEPTH:0]        rx_fifo_count;

    wire                       dominant_bit;
    wire                       recessive_bit;
    wire                       start_of_frame;
    wire                       end_of_frame;
    wire                       stuff_error;
    wire                       form_error_det;
    wire                       crc_error_det;

    assign dominant_bit = 1'b0;
    assign recessive_bit = 1'b1;
    assign rx_dominant = (can_rx == dominant_bit);
    assign start_of_frame = rx_dominant && (state == IDLE);
    assign end_of_frame = !rx_dominant && (state == END_OF_FR);

    always @(posedge clk_can or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            rx_ready <= 1'b0;
            rx_overflow <= 1'b0;
            error_frame <= 1'b0;
            rx_id <= '0;
            rx_data <= '0;
        end else begin
            rx_ready <= 1'b0;
            error_frame <= 1'b0;

            case (state)
                IDLE: begin
                    rx_fifo_empty <= (rx_fifo_count == 0);
                    if (start_of_frame) begin
                        state <= RECEIVE;
                        bit_counter <= 10;
                        rx_id_reg <= '0;
                    end
                end
                RECEIVE: begin
                    if (bit_counter > 0) begin
                        bit_counter <= bit_counter - 1;
                        rx_id_reg[10-bit_counter] <= rx_dominant;
                    end else begin
                        state <= CHECK_ID;
                    end
                end
                CHECK_ID: begin
                    rtr_bit <= rx_dominant;
                    ide_bit <= rx_dominant;
                    if (ide_bit) begin
                        state <= RECEIVE;
                        bit_counter <= 17;
                    end else begin
                        state <= CHECK_DLC;
                        bit_counter <= 3;
                    end
                end
                CHECK_DLC: begin
                    if (bit_counter > 0) begin
                        bit_counter <= bit_counter - 1;
                        dlc_reg[4-bit_counter] <= rx_dominant;
                    end else begin
                        if (dlc_reg > 8) begin
                            state <= ERROR_FR;
                        end else begin
                            state <= DATA_PHASE;
                            bit_counter <= dlc_reg * 8 - 1;
                        end
                    end
                end
                DATA_PHASE: begin
                    if (bit_counter > 0) begin
                        bit_counter <= bit_counter - 1;
                        if (bit_counter < 32) begin
                            rx_data_reg[31-bit_counter] <= rx_dominant;
                        end else begin
                            rx_data_reg[63-(bit_counter-32)] <= rx_dominant;
                        end
                    end else begin
                        state <= CHECK_CRC;
                        bit_counter <= 14;
                        crc_reg <= '0;
                        crc_counter <= 0;
                    end
                end
                CHECK_CRC: begin
                    if (bit_counter > 0) begin
                        bit_counter <= bit_counter - 1;
                        if (bit_counter < 14) begin
                            crc_reg[14-bit_counter] <= rx_dominant;
                        end
                    end else begin
                        state <= ACK_SLOT;
                    end
                end
                ACK_SLOT: begin
                    if (!rx_dominant) begin
                        rx_fifo_full <= (rx_fifo_count == FIFO_DEPTH);
                        if (!rx_fifo_full) begin
                            rx_id <= rx_id_reg;
                            rx_data <= rx_data_reg;
                            rx_ready <= 1'b1;
                        end else begin
                            rx_overflow <= 1'b1;
                        end
                    end
                    state <= END_OF_FR;
                    bit_counter <= 6;
                end
                END_OF_FR: begin
                    if (bit_counter > 0) begin
                        bit_counter <= bit_counter - 1;
                    end else begin
                        if (rx_dominant) begin
                            state <= ERROR_FR;
                            error_frame <= 1'b1;
                        end else begin
                            state <= IDLE;
                        end
                    end
                end
                ERROR_FR: begin
                    state <= IDLE;
                end
            endcase
        end
    end

    always @(posedge clk_can or negedge rst_n) begin
        if (!rst_n) begin
            rx_fifo_wr_ptr <= '0;
            rx_fifo_rd_ptr <= '0;
            rx_fifo_count <= '0;
        end else begin
            if (rx_ready && !rx_fifo_full) begin
                rx_fifo_wr_ptr <= rx_fifo_wr_ptr + 1;
            end
            if (rx_ack && !rx_fifo_empty) begin
                rx_fifo_rd_ptr <= rx_fifo_rd_ptr + 1;
            end
            rx_fifo_count <= rx_fifo_wr_ptr - rx_fifo_rd_ptr;
        end
    end

endmodule
