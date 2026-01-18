//-----------------------------------------------------------------------------
// File: pcie_data_link_layer.sv
// Description: PCIe Data Link Layer (DLLP/AckNak Protocol)
// Author: YaoGuang SoC Team
// Date: 2026-01-19
//-----------------------------------------------------------------------------

`timescale 1ps/1ps

module pcie_data_link_layer #(
    parameter LANES = 8
) (
    input  logic                                clk_sys,
    input  logic                                clk_phy,
    input  logic                                rst_n_sys,
    input  logic                                rst_n_phy,
    input  logic [255:0]                        tl_tx_data,
    output logic [255:0]                        tl_rx_data,
    input  logic                                tl_tx_valid,
    output logic                                tl_tx_ready,
    output logic                                tl_rx_valid,
    input  logic                                tl_rx_ready,
    input  logic [31:0]                         tl_tx_hdr,
    output logic [31:0]                         tl_rx_hdr,
    input  logic                                tl_tx_end,
    output logic                                tl_rx_end,
    output logic                                dll_tx_seq_num,
    input  logic                                dll_rx_seq_num,
    output logic                                dll_tx_ack,
    output logic                                dll_rx_ack,
    output logic [15:0]                         dll_tx_credits,
    input  logic [15:0]                         dll_rx_credits,
    output logic [LANES*32-1:0]                 phy_tx_data,
    input  logic [LANES*32-1:0]                 phy_rx_data,
    output logic                                phy_tx_valid,
    input  logic                                phy_rx_valid,
    input  logic                                phy_tx_ready,
    output logic                                phy_rx_ready,
    output logic [5:0]                          phy_tx_status,
    input  logic [5:0]                          phy_rx_status,
    output logic                                link_up,
    output logic [3:0]                          link_width,
    output logic [2:0]                          link_rate,
    input  logic                                link_training
);

    localparam DLLP_SIZE = 8;
    localparam TLP_MAX_SIZE = 1024;
    localparam ACK_TIMEOUT = 32'd50000;
    localparam SEQ_NUM_WIDTH = 12;

    // DLLP Types
    typedef enum logic [7:0] {
        DLLP_ACK = 8'b0000_0000,
        DLLP_NAK = 8'b0001_0000,
        DLLP_PM_ENTER_L1 = 8'b0010_0001,
        DLLP_PM_ENTER_L23 = 8'b0010_0010,
        DLLP_PM_ACTIVE_STATE = 8'b0010_0011,
        DLLP_INIT_FC_0 = 8'b0100_0000,
        DLLP_INIT_FC_1 = 8'b0100_0001,
        DLLP_INIT_FC_2 = 8'b0100_0010,
        DLLP_UPDATE_FC_0 = 8'b0110_0000,
        DLLP_UPDATE_FC_1 = 8'b0110_0001,
        DLLP_UPDATE_FC_2 = 8'b0110_0010,
        DLLP_VENDOR = 8'b0111_0000
    } dllp_type_t;

    // Flow Control Credit Types
    typedef enum logic [2:0] {
        FC_PH = 3'b000,
        FC_PD = 3'b001,
        FC_NPH = 3'b010,
        FC_NPD = 3'b011,
        FC_CPLH = 3'b100,
        FC_CPLD = 3'b101
    } fc_type_t;

    // Internal Registers
    logic [SEQ_NUM_WIDTH-1:0]                   tx_seq_num;
    logic [SEQ_NUM_WIDTH-1:0]                   rx_seq_num;
    logic [SEQ_NUM_WIDTH-1:0]                   tx_ack_seq;
    logic [SEQ_NUM_WIDTH-1:0]                   rx_ack_seq;
    logic [SEQ_NUM_WIDTH-1:0]                   nak_seq_num;
    logic [ACK_TIMEOUT-1:0]                     ack_timer;
    logic                                        ack_timeout;
    logic                                        nak_pending;
    logic [31:0]                                 replay_buf [0:127];
    logic [15:0]                                 replay_cnt;
    logic                                        replay_overflow;

    // Flow Control Counters
    logic [11:0]                                 fc_ph_avail;
    logic [11:0]                                 fc_pd_avail;
    logic [11:0]                                 fc_nph_avail;
    logic [11:0]                                 fc_npd_avail;
    logic [11:0]                                 fc_cplh_avail;
    logic [11:0]                                 fc_cpld_avail;
    logic [11:0]                                 fc_ph_init;
    logic [11:0]                                 fc_pd_init;
    logic [11:0]                                 fc_cplh_init;
    logic [11:0]                                 fc_cpld_init;

    // Transmit State Machine
    typedef enum logic [3:0] {
        TX_DLL_IDLE,
        TX_TLP_SEND,
        TX_DLLP_SEND,
        TX_ACK_SEND,
        TX_REPLAY
    } tx_dll_state_t;

    tx_dll_state_t tx_dll_state;

    // Receive State Machine
    typedef enum logic [3:0] {
        RX_DLL_IDLE,
        RX_TLP_RECV,
        RX_DLLP_RECV,
        RX_ACK_RECV,
        RX_NAK_RECV,
        RX_ERR_RECOVERY
    } rx_dll_state_t;

    rx_dll_state_t rx_dll_state;

    // TLP Transmit Path
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            tx_seq_num <= '0;
            tx_ack_seq <= '0;
            replay_cnt <= '0;
            ack_timer <= '0;
            tx_dll_state <= TX_DLL_IDLE;
            tl_tx_ready <= 1'b0;
            phy_tx_valid <= 1'b0;
            dll_tx_seq_num <= 1'b0;
            dll_tx_ack <= 1'b0;
        end else begin
            case (tx_dll_state)
                TX_DLL_IDLE: begin
                    if (tl_tx_valid) begin
                        tl_tx_ready <= 1'b1;
                        replay_buf[replay_cnt] <= {tl_tx_hdr, tl_tx_data};
                        tx_seq_num <= tx_seq_num + 1;
                        replay_cnt <= replay_cnt + 1;
                        ack_timer <= ACK_TIMEOUT;
                        tx_dll_state <= TX_TLP_SEND;
                    end
                end
                TX_TLP_SEND: begin
                    tl_tx_ready <= 1'b0;
                    if (phy_tx_ready) begin
                        phy_tx_valid <= 1'b1;
                        phy_tx_data <= {tl_tx_data[255:0], tl_tx_hdr[31:0], 8'b00000000};
                        dll_tx_seq_num <= tx_seq_num[0];
                        tx_dll_state <= TX_DLL_IDLE;
                    end
                end
            endcase
        end
    end

    // DLLP Transmit Path
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            dll_tx_credits <= 16'd256;
            phy_tx_valid <= 1'b0;
            phy_tx_data <= '0;
        end else begin
            // Send ACK DLLP
            if (rx_ack_seq != tx_ack_seq) begin
                phy_tx_valid <= 1'b1;
                phy_tx_data <= {24'b0, DLLP_ACK, rx_ack_seq[7:0], 16'b0};
                tx_ack_seq <= rx_ack_seq;
            end
            // Send NAK DLLP
            else if (nak_pending) begin
                phy_tx_valid <= 1'b1;
                phy_tx_data <= {24'b0, DLLP_NAK, nak_seq_num[7:0], 16'b0};
                nak_pending <= 1'b0;
            end
            // Update credits periodically
            else if (credit_update_timer == 0) begin
                phy_tx_valid <= 1'b1;
                phy_tx_data <= {24'b0, DLLP_UPDATE_FC_0, fc_npd_avail[11:4], fc_npd_avail[3:0], fc_cpld_avail[11:4], fc_cpld_avail[3:0]};
            end
        end
    end

    // TLP Receive Path
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            rx_seq_num <= '0;
            rx_ack_seq <= '0;
            nak_seq_num <= '0;
            rx_dll_state <= RX_DLL_IDLE;
            tl_rx_valid <= 1'b0;
            phy_rx_ready <= 1'b0;
            dll_rx_seq_num <= 1'b0;
            dll_rx_ack <= 1'b0;
        end else begin
            case (rx_dll_state)
                RX_DLL_IDLE: begin
                    phy_rx_ready <= 1'b1;
                    if (phy_rx_valid) begin
                        if (phy_rx_data[7:0] inside {8'b0000_0000, 8'b0010_0010, 8'b0010_0011}) begin
                            rx_dll_state <= RX_TLP_RECV;
                        end else begin
                            rx_dll_state <= RX_DLLP_RECV;
                        end
                    end
                end
                RX_TLP_RECV: begin
                    dll_rx_seq_num <= phy_rx_data[8];
                    tl_rx_hdr <= phy_rx_data[39:8];
                    tl_rx_data <= phy_rx_data[255:40];
                    tl_rx_valid <= 1'b1;
                    rx_seq_num <= rx_seq_num + 1;
                    rx_dll_state <= RX_DLL_IDLE;
                    if (phy_rx_data[8] != tx_seq_num) begin
                        nak_seq_num <= rx_seq_num;
                        nak_pending <= 1'b1;
                        rx_dll_state <= RX_ERR_RECOVERY;
                    end
                end
                RX_DLLP_RECV: begin
                    case (phy_rx_data[7:0])
                        DLLP_ACK: begin
                            rx_ack_seq <= phy_rx_data[15:8];
                            dll_rx_ack <= 1'b1;
                            replay_buf[phy_rx_data[15:8]] <= '0;
                        end
                        DLLP_NAK: begin
                            tx_seq_num <= phy_rx_data[15:8];
                            ack_timer <= ACK_TIMEOUT;
                            tx_dll_state <= TX_REPLAY;
                        end
                        default: begin
                            // Update flow control credits
                            update_credits(phy_rx_data);
                        end
                    endcase
                    rx_dll_state <= RX_DLL_IDLE;
                end
                RX_REPLAY: begin
                    if (ack_timeout) begin
                        tx_dll_state <= TX_REPLAY;
                    end
                end
            endcase
        end
    end

    // Flow Control Credit Update
    function void update_credits(input [31:0] dllp_data);
        case (dllp_data[7:0])
            DLLP_INIT_FC_0, DLLP_UPDATE_FC_0: begin
                fc_ph_avail <= dllp_data[19:16];
                fc_pd_avail <= dllp_data[23:20];
                fc_nph_avail <= dllp_data[27:24];
                fc_npd_avail <= dllp_data[31:28];
            end
            DLLP_INIT_FC_1, DLLP_UPDATE_FC_1: begin
                fc_cplh_avail <= dllp_data[19:16];
                fc_cpld_avail <= dllp_data[23:20];
            end
        endcase
    endfunction

    // Ack Timeout Monitor
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            ack_timer <= ACK_TIMEOUT;
            ack_timeout <= 1'b0;
        end else begin
            if (tx_seq_num != tx_ack_seq) begin
                if (ack_timer > 0) begin
                    ack_timer <= ack_timer - 1;
                end else begin
                    ack_timeout <= 1'b1;
                    tx_dll_state <= TX_REPLAY;
                end
            end else begin
                ack_timer <= ACK_TIMEOUT;
                ack_timeout <= 1'b0;
            end
        end
    end

    // Replay Buffer Management
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            replay_cnt <= '0;
            replay_overflow <= 1'b0;
        end else begin
            if (tx_seq_num - tx_ack_seq > 100) begin
                replay_overflow <= 1'b1;
            end else begin
                replay_overflow <= 1'b0;
            end
        end
    end

    // Link Training and Status
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            link_up <= 1'b0;
            link_width <= 4'b0000;
            link_rate <= 3'b000;
        end else begin
            if (phy_rx_status[0] && phy_rx_status[1]) begin
                link_up <= 1'b1;
                link_width <= phy_rx_status[3:2];
                link_rate <= phy_rx_status[6:4];
            end else begin
                link_up <= 1'b0;
            end
        end
    end

    // Lane Deskew
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            for (int i = 0; i < LANES; i++) begin
                lane_align_reg[i] <= '0;
            end
        end else begin
            if (phy_rx_valid) begin
                for (int i = 0; i < LANES; i++) begin
                    if (phy_rx_data[i*32+:8] == 8'b10111011) begin
                        lane_align_reg[i] <= i;
                    end
                end
            end
        end
    end

endmodule
