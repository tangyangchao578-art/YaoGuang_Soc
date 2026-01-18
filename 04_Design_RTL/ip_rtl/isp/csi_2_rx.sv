// ============================================================
// Project: YaoGuang ISP
// Module:  csi_2_rx.sv
// Description: MIPI CSI-2 Receiver
// ============================================================

`timescale 1ns/1ps

module csi_2_rx #(
    parameter int NUM_LANES      = 16,
    parameter int DATA_WIDTH     = 16,
    parameter int MAX_PACKET_LEN = 65536
) (
    // Clock & Reset
    input  logic                    clk_i,
    input  logic                    rst_n_i,

    // MIPI D-PHY Interface
    input  logic [NUM_LANES-1:0]    csi_d_p_i,
    input  logic [NUM_LANES-1:0]    csi_d_n_i,
    input  logic                    csi_clk_p_i,
    input  logic                    csi_clk_n_i,

    // Output
    output logic [DATA_WIDTH-1:0]   raw_data_o,
    output logic                    raw_valid_o,
    output logic                    raw_sop_o,
    output logic                    raw_eop_o,
    output logic [1:0]              raw_vc_o,
    output logic [5:0]              raw_dt_o,
    output logic                    lock_o,
    output logic                    error_o
);

    // PHY Interface Signals
    logic [NUM_LANES-1:0]           lane_data_p;
    logic [NUM_LANES-1:0]           lane_data_n;
    logic                           clk_p;
    logic                           clk_n;
    logic [NUM_LANES-1:0]           lane_data_valid;
    logic [NUM_LANES-1:0]           lane_data[NUM_LANES-1:0];
    logic                           lane_clk;

    // Clock Domain Crossing
    logic                           clk_rx;
    logic                           clk_byte;
    logic                           byte_valid;
    logic [7:0]                     byte_data[NUM_LANES-1:0];
    logic [7:0]                     rx_byte;

    // Packet Parsing
    logic [15:0]                    packet_word;
    logic [15:0]                    packet_count;
    logic                           in_packet;
    logic [1:0]                     current_vc;
    logic [5:0]                     current_dt;
    logic [15:0]                    word_count;
    logic [15:0]                    payload_len;

    // State Machine
    typedef enum logic [2:0] {
        IDLE,
        SYNC,
        HEADER,
        PAYLOAD,
        CHECKSUM,
        TRAILER
    } state_t;

    state_t                         state;
    state_t                         next_state;

    // CRC Check
    logic [15:0]                    crc_in;
    logic [15:0]                    crc_calc;
    logic                           crc_error;

    // ============================================================
    // D-PHY Deserialization
    // ============================================================
    generate
        for (genvar i = 0; i < NUM_LANES; i++) begin : gen_dphy
            dphy_deserializer #(
                .DATA_RATE(4.5)
            ) u_dphy_deser (
                .clk_p_i       (csi_clk_p_i),
                .clk_n_i       (csi_clk_n_i),
                .data_p_i      (csi_d_p_i[i]),
                .data_n_i      (csi_d_n_i[i]),
                .clk_o         (lane_clk),
                .data_o        (lane_data[i]),
                .valid_o       (lane_data_valid[i])
            );
        end
    endgenerate

    // Clock multiplexer for CDC
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            lock_o <= '0;
        end else begin
            // Check for valid clock lock
            lock_o <= &lane_data_valid;
        end
    end

    // ============================================================
    // Lane Merging (Byte Level)
    // ============================================================
    always_comb begin
        rx_byte = '0;
        for (int i = 0; i < NUM_LANES; i++) begin
            if (lane_data_valid[i]) begin
                rx_byte = lane_data[i];
            end
        end
    end

    // ============================================================
    // Packet State Machine
    // ============================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            state <= IDLE;
            packet_word <= '0;
            packet_count <= '0;
            in_packet <= '0;
            current_vc <= '0;
            current_dt <= '0;
            word_count <= '0;
            payload_len <= '0;
            crc_in <= '0;
            raw_valid_o <= '0;
            raw_sop_o <= '0;
            raw_eop_o <= '0;
            raw_data_o <= '0;
            raw_vc_o <= '0;
            raw_dt_o <= '0;
            error_o <= '0;
        end else begin
            state <= next_state;
            raw_valid_o <= '0;
            raw_sop_o <= '0;
            raw_eop_o <= '0;

            case (state)
                IDLE: begin
                    // Wait for packet start (Sync pattern)
                    if (rx_byte == 8'hB8) begin
                        next_state = HEADER;
                        raw_sop_o <= '1;
                    end
                end

                HEADER: begin
                    // DI, VC (byte 0)
                    current_vc <= rx_byte[7:6];
                    current_dt <= rx_byte[5:0];
                    word_count[15:8] <= rx_byte;
                    packet_word <= {8'h00, rx_byte};

                    // WC[15:8] (byte 1)
                    word_count[7:0] <= rx_byte;
                    payload_len <= {word_count[15:8], rx_byte};
                    packet_word <= {packet_word[15:8], rx_byte};

                    if (payload_len > 0) begin
                        in_packet <= '1;
                        packet_count <= payload_len;
                        next_state = PAYLOAD;
                    end else begin
                        next_state = CHECKSUM;
                    end
                end

                PAYLOAD: begin
                    if (packet_count > 0) begin
                        raw_data_o <= rx_byte;
                        raw_valid_o <= '1;
                        raw_vc_o <= current_vc;
                        raw_dt_o <= current_dt;
                        packet_count <= packet_count - 1;
                        packet_word <= {packet_word[7:0], rx_byte};

                        if (packet_count == 1) begin
                            next_state = CHECKSUM;
                        end
                    end
                end

                CHECKSUM: begin
                    crc_in <= {rx_byte, packet_word[15:8]};
                    packet_word <= '0;
                    next_state = TRAILER;
                end

                TRAILER: begin
                    raw_eop_o <= '1;
                    crc_error <= (crc_calc != crc_in);
                    error_o <= crc_error;
                    in_packet <= '0;
                    next_state = IDLE;
                end

                default: begin
                    next_state = IDLE;
                end
            endcase
        end
    end

    // ============================================================
    // CRC Calculation (CRC-16 CCITT)
    // ============================================================
    always_ff @(posedge clk_i) begin
        if (in_packet && raw_valid_o) begin
            crc_calc <= crc16_ccitt(rx_byte, crc_calc);
        end else if (state == IDLE) begin
            crc_calc <= 16'hFFFF;
        end
    end

    function automatic [15:0] crc16_ccitt(
        input [7:0] data,
        input [15:0] crc
    );
        integer i;
        begin
            crc = crc ^ {data, 8'h00};
            for (i = 0; i < 8; i++) begin
                if (crc[15]) begin
                    crc = {crc[14:0], 1'b0} ^ 16'h1021;
                end else begin
                    crc = {crc[14:0], 1'b0};
                end
            end
            crc16_ccitt = crc;
        end
    endfunction

endmodule
