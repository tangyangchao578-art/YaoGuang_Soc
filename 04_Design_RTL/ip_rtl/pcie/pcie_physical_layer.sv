//-----------------------------------------------------------------------------
// File: pcie_physical_layer.sv
// Description: PCIe Physical Layer (PCS/PMA for Gen4)
// Author: YaoGuang SoC Team
// Date: 2026-01-19
//-----------------------------------------------------------------------------

`timescale 1ps/1ps

module pcie_physical_layer #(
    parameter LANES = 8,
    parameter PCS_DATA_WIDTH = 64
) (
    input  logic                                clk_phy,
    input  logic                                rst_n_phy,
    input  logic [LANES*PCS_DATA_WIDTH-1:0]     phy_tx_data,
    output logic [LANES*PCS_DATA_WIDTH-1:0]     phy_rx_data,
    input  logic                                phy_tx_valid,
    output logic                                phy_tx_ready,
    output logic                                phy_rx_valid,
    input  logic                                phy_rx_ready,
    input  logic [5:0]                          phy_tx_status,
    output logic [5:0]                          phy_rx_status,
    output logic [LANES-1:0]                    tx_data_p,
    output logic [LANES-1:0]                    tx_data_n,
    input  logic [LANES-1:0]                    rx_data_p,
    input  logic [LANES-1:0]                    rx_data_n,
    output logic                                tx_clk_p,
    output logic                                tx_clk_n,
    input  logic                                rx_clk_p,
    input  logic                                rx_clk_n,
    output logic                                tx_elec_idle,
    input  logic                                phy_ready,
    input  logic                                phy_status
);

    localparam PMA_DATA_WIDTH = 32;
    localparam SCRAMBLER_POLY = 16'h800D;

    // 128b/130b Encoding
    typedef enum logic [1:0] {
        BLOCK_DATA = 2'b00,
        BLOCK_SKP = 2'b01,
        BLOCK_IDLE = 2'b10,
        BLOCK_CTRL = 2'b11
    } block_type_t;

    localparam [7:0] SKIPOrderedSet = 8'b10111011;
    localparam [7:0] COMOrderedSet = 8'b11011100;
    localparam [7:0] IDLODataSet = 8'b10111100;

    // Scrambler State
    logic [15:0]                                scrambler_state [0:LANES-1];
    logic                                        scrambler_enable;
    logic [7:0]                                 skip_interval;

    // Elastic Buffer
    logic [7:0]                                 elastic_buffer [0:LANES-1][0:63];
    logic [6:0]                                 buffer_wr_ptr [0:LANES-1];
    logic [6:0]                                 buffer_rd_ptr [0:LANES-1];
    logic                                        buffer_overflow [0:LANES-1];
    logic                                        buffer_underflow [0:LANES-1];

    // Sync State Machine
    typedef enum logic [2:0] {
        SYNC_ACQUIRE,
        SYNC_CHECK,
        SYNC_LOCK,
        SYNC_MONITOR
    } sync_state_t;

    sync_state_t sync_state [0:LANES-1];
    logic [3:0]                                  sync_count [0:LANES-1];

    // TX Path (PMA)
    genvar lane;
    generate
        for (lane = 0; lane < LANES; lane++) begin : tx_lane_gen
            always_ff @(posedge clk_phy or negedge rst_n_phy) begin
                if (!rst_n_phy) begin
                    scrambler_state[lane] <= 16'hFFFF;
                    skip_counter <= '0;
                end else begin
                    // Scramble data
                    if (phy_tx_valid) begin
                        scrambler_state[lane] <= update_scrambler(scrambler_state[lane], phy_tx_data[lane*PCS_DATA_WIDTH+:8]);
                    end
                    // Skip insertion
                    if (skip_counter == 0) begin
                        tx_skip_gen <= 1'b1;
                        skip_counter <= skip_interval;
                    end else begin
                        skip_counter <= skip_counter - 1;
                    end
                end
            end

            // 128b/130b Encoder
            always_ff @(posedge clk_phy or negedge rst_n_phy) begin
                if (!rst_n_phy) begin
                    tx_enc_data <= '0;
                    tx_enc_valid <= 1'b0;
                end else begin
                    if (phy_tx_valid) begin
                        tx_enc_data[129:128] <= BLOCK_DATA;
                        tx_enc_data[127:0] <= scramble(phy_tx_data[lane*PCS_DATA_WIDTH+:128]);
                        tx_enc_valid <= 1'b1;
                    end else if (tx_skip_gen) begin
                        tx_enc_data[129:128] <= BLOCK_SKP;
                        tx_enc_data[127:0] <= {SKIPOrderedSet, 120'b0};
                        tx_enc_valid <= 1'b1;
                    end else begin
                        tx_enc_valid <= 1'b0;
                    end
                end
            end

            // SerDes TX
            always_ff @(posedge clk_phy) begin
                tx_ser_data <= tx_enc_data;
            end
        end
    endgenerate

    // RX Path (PMA)
    generate
        for (lane = 0; lane < LANES; lane++) begin : rx_lane_gen
            // Deserializer
            always_ff @(posedge clk_phy) begin
                rx_des_data <= rx_ser_data;
            end

            // 128b/130b Decoder
            always_ff @(posedge clk_phy or negedge rst_n_phy) begin
                if (!rst_n_phy) begin
                    sync_state[lane] <= SYNC_ACQUIRE;
                    sync_count[lane] <= '0;
                    phy_rx_valid <= 1'b0;
                end else begin
                    case (sync_state[lane])
                        SYNC_ACQUIRE: begin
                            if (rx_des_data[129:128] == 2'b01) begin
                                sync_count[lane] <= sync_count[lane] + 1;
                                if (sync_count[lane] >= 8) begin
                                    sync_state[lane] <= SYNC_CHECK;
                                    sync_count[lane] <= '0;
                                end
                            end else begin
                                sync_count[lane] <= '0;
                            end
                        end
                        SYNC_CHECK: begin
                            if (rx_des_data[129:128] == 2'b01) begin
                                sync_count[lane] <= sync_count[lane] + 1;
                                if (sync_count[lane] >= 4) begin
                                    sync_state[lane] <= SYNC_LOCK;
                                end
                            end else begin
                                sync_state[lane] <= SYNC_ACQUIRE;
                            end
                        end
                        SYNC_LOCK: begin
                            phy_rx_valid <= 1'b1;
                            phy_rx_data[lane*PCS_DATA_WIDTH+:128] <= descramble(rx_des_data[127:0]);
                            if (rx_des_data[129:128] == BLOCK_SKP) begin
                                skip_processing[lane] <= 1'b1;
                            end
                        end
                    endcase
                end
            end
        end
    endgenerate

    // Scrambler Function
    function [127:0] scramble(input [127:0] data);
        integer i;
        reg [15:0] lfsr;
        begin
            lfsr = scrambler_state[0];
            for (i = 0; i < 128; i++) begin
                scramble[i] = data[i] ^ lfsr[0] ^ lfsr[1] ^ lfsr[4] ^ lfsr[7];
                lfsr = {lfsr[0], lfsr[15:1]};
            end
        end
    endfunction

    // Descrambler Function
    function [127:0] descramble(input [127:0] data);
        integer i;
        reg [15:0] lfsr;
        begin
            lfsr = scrambler_state[0];
            for (i = 0; i < 128; i++) begin
                descramble[i] = data[i] ^ lfsr[0] ^ lfsr[1] ^ lfsr[4] ^ lfsr[7];
                lfsr = {lfsr[0], lfsr[15:1]};
            end
        end
    endfunction

    // Update Scrambler State
    function [15:0] update_scrambler(input [15:0] state, input [7:0] data);
        reg [15:0] new_state;
        begin
            new_state = {state[6:0], state[7] ^ state[5] ^ state[4] ^ state[2]};
            update_scrambler = new_state;
        end
    endfunction

    // Electrical Idle Control
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            tx_elec_idle <= 1'b1;
            phy_tx_ready <= 1'b0;
        end else begin
            if (!phy_ready || power_state == D3) begin
                tx_elec_idle <= 1'b1;
                phy_tx_ready <= 1'b0;
            end else begin
                tx_elec_idle <= 1'b0;
                phy_tx_ready <= 1'b1;
            end
        end
    end

    // Lane Polarity Inversion
    logic [LANES-1:0]                            polarity_inv;
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            polarity_inv <= '0;
        end else begin
            if (phy_rx_status[5]) begin
                polarity_inv <= polarity_inv | lane_polarity_errors;
            end
        end
    end

    // PHY Status
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            phy_rx_status <= '0;
        end else begin
            phy_rx_status[0] <= phy_ready;
            phy_rx_status[1] <= link_established;
            phy_rx_status[2] <= rx_locked;
            phy_rx_status[3] <= lane_count_detected;
            phy_rx_status[4] <= data_rate_detected;
            phy_rx_status[5] <= parity_error;
        end
    end

    // Link Training State Machine (LTSSM)
    typedef enum logic [4:0] {
        LTSSM_DETECT,
        LTSSM_POLLING,
        LTSSM_CONFIG,
        LTSSM_L0,
        LTSSM_L0s,
        LTSSM_L1,
        LTSSM_L2,
        LTSSM_HOT_RESET,
        LTSSM_DISABLED,
        LTSSM_LOOPBACK
    } ltssm_state_t;

    ltssm_state_t ltssm_state;

    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            ltssm_state <= LTSSM_DETECT;
            link_established <= 1'b0;
        end else begin
            case (ltssm_state)
                LTSSM_DETECT: begin
                    if (phy_rx_valid && rx_data_detect) begin
                        ltssm_state <= LTSSM_POLLING;
                    end
                end
                LTSSM_POLLING: begin
                    if (tx_eq_complete && rx_eq_complete) begin
                        ltssm_state <= LTSSM_CONFIG;
                    end
                end
                LTSSM_CONFIG: begin
                    if (lane_width_detected && link_width_negotiated) begin
                        ltssm_state <= LTSSM_L0;
                    end
                end
                LTSSM_L0: begin
                    link_established <= 1'b1;
                    if (link_error) begin
                        ltssm_state <= LTSSM_DETECT;
                    end else if (power_down_request) begin
                        ltssm_state <= LTSSM_L1;
                    end
                end
                LTSSM_L1: begin
                    if (wakeup_request) begin
                        ltssm_state <= LTSSM_L0;
                    end
                end
                default: ltssm_state <= LTSSM_DETECT;
            endcase
        end
    end

endmodule
