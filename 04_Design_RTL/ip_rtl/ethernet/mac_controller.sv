//-----------------------------------------------------------------------------
// File: mac_controller.sv
// Description: Ethernet MAC Controller (10G/1G)
// Author: YaoGuang SoC Team
// Date: 2026-01-19
//-----------------------------------------------------------------------------

`timescale 1ps/1ps

module mac_controller #(
    parameter PORT_ID = 0,
    parameter TSN_ENABLE = 1
) (
    input  logic                                clk_sys,
    input  logic                                clk_phy,
    input  logic                                rst_n_sys,
    input  logic                                rst_n_phy,
    output logic                                tx_axis_tvalid,
    output logic                                tx_axis_tlast,
    output logic [6:0]                          tx_axis_tuser,
    output logic [127:0]                        tx_axis_tdata,
    input  logic                                tx_axis_tready,
    input  logic                                rx_axis_tvalid,
    input  logic                                rx_axis_tlast,
    input  logic [6:0]                          rx_axis_tuser,
    input  logic [127:0]                        rx_axis_tdata,
    output logic                                rx_axis_tready,
    output logic                                mac_tx_clk,
    output logic                                mac_rx_clk,
    output logic                                mac_tx_en,
    output logic                                mac_tx_err,
    output logic [7:0]                          mac_tx_data,
    input  logic                                mac_rx_dv,
    input  logic                                mac_rx_err,
    input  logic [7:0]                          mac_rx_data,
    input  logic                                mac_col,
    input  logic                                mac_crs,
    input  logic                                link_status,
    input  logic [1:0]                          link_speed,
    input  logic                                duplex_mode,
    output logic [7:0]                          eth_intr,
    output logic [63:0]                         stats_tx_bytes,
    output logic [63:0]                         stats_rx_bytes,
    output logic [31:0]                         stats_tx_pkts,
    output logic [31:0]                         stats_rx_pkts,
    output logic [7:0]                          stats_tx_errors,
    output logic [7:0]                          stats_rx_errors
);

    localparam MAX_JUMBO_SIZE = 16384;
    localparam MIN_FRAME_SIZE = 64;
    localparam MAX_FRAME_SIZE = 1518;

    // MAC Control
    logic                                        mac_enable;
    logic                                        tx_enable;
    logic                                        rx_enable;
    logic                                        promiscuous;
    logic                                        pause_enable;
    logic [15:0]                                 pause_value;

    // MAC Address
    logic [47:0]                                 mac_addr;
    logic [47:0]                                 mac_addr_mask;

    // Frame Check Sequence
    logic [31:0]                                 tx_crc;
    logic [31:0]                                 rx_crc;
    logic                                        crc_error;

    // Inter-packet Gap
    logic [7:0]                                  ipg_counter;
    logic                                        ipg_ready;

    // TX State Machine
    typedef enum logic [3:0] {
        TX_IDLE,
        TX_PREAMBLE,
        TX_SFD,
        TX_DATA,
        TX_PAD,
        TX_CRC,
        TX_IPG,
        TX_COLLISION
    } tx_state_t;

    tx_state_t tx_state;

    // RX State Machine
    typedef enum logic [3:0] {
        RX_IDLE,
        RX_PREAMBLE,
        RX_SFD,
        RX_DATA,
        RX_CRC,
        RX_DROP,
        RX_PAUSE
    } rx_state_t;

    rx_state_t rx_state;

    // TX Data Path
    logic [7:0]                                  tx_data_reg;
    logic                                        tx_valid_reg;
    logic [15:0]                                 tx_byte_counter;
    logic [15:0]                                 tx_frame_length;
    logic                                        tx_underrun;

    // RX Data Path
    logic [7:0]                                  rx_data_reg;
    logic                                        rx_valid_reg;
    logic [15:0]                                 rx_byte_counter;
    logic [15:0]                                 rx_frame_length;
    logic                                        rx_frame_error;
    logic                                        rx_crc_check;

    // Statistics Counters
    logic [63:0]                                 tx_byte_count;
    logic [63:0]                                 rx_byte_count;
    logic [31:0]                                 tx_pkt_count;
    logic [31:0]                                 rx_pkt_count;
    logic [7:0]                                  tx_error_count;
    logic [7:0]                                  rx_error_count;

    // Pause Frame
    logic                                        pause_frame_rx;
    logic [15:0]                                 pause_timer;

    // VLAN Tag
    logic                                        vlan_detect;
    logic [15:0]                                 vlan_tag;

    // TSN Features (if enabled)
    generate
        if (TSN_ENABLE) begin : tsn_features
            logic                                tsm_available;
            logic [79:0]                         tsm_value;
            logic                                frame_preemption;
            logic                                qbv_gate_control;
        end
    endgenerate

    // TX MAC Clock Generation
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            mac_tx_clk <= 1'b0;
        end else begin
            case (link_speed)
                2'b10: mac_tx_clk <= !mac_tx_clk;      // 125MHz for 1G
                2'b01: mac_tx_clk <= !mac_tx_clk;      // 125MHz for 100M
                2'b00: mac_tx_clk <= !mac_tx_clk;      // 25MHz for 10M
                default: mac_tx_clk <= !mac_tx_clk;
            endcase
        end
    end

    // RX MAC Clock Generation
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            mac_rx_clk <= 1'b0;
        end else begin
            mac_rx_clk <= !mac_rx_clk;
        end
    end

    // TX State Machine
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            tx_state <= TX_IDLE;
            tx_enable <= 1'b0;
            tx_byte_counter <= '0;
            tx_axis_tvalid <= 1'b0;
            tx_axis_tlast <= 1'b0;
            tx_axis_tdata <= '0;
            tx_axis_tuser <= '0;
            ipg_counter <= '0;
        end else begin
            case (tx_state)
                TX_IDLE: begin
                    if (tx_axis_tvalid && tx_axis_tready && ipg_ready) begin
                        tx_state <= TX_PREAMBLE;
                        tx_byte_counter <= '0;
                        tx_frame_length <= 0;
                    end
                end
                TX_PREAMBLE: begin
                    if (tx_byte_counter < 7) begin
                        tx_axis_tdata[127:120] <= 8'h55;
                        tx_byte_counter <= tx_byte_counter + 1;
                    end else begin
                        tx_state <= TX_SFD;
                        tx_axis_tdata[127:120] <= 8'hD5;
                    end
                end
                TX_SFD: begin
                    tx_state <= TX_DATA;
                    tx_byte_counter <= '0;
                end
                TX_DATA: begin
                    if (tx_axis_tvalid && tx_axis_tready) begin
                        tx_byte_counter <= tx_byte_counter + 16;
                        tx_frame_length <= tx_frame_length + 16;
                        if (tx_axis_tlast) begin
                            if (tx_frame_length + 16 < MIN_FRAME_SIZE) begin
                                tx_state <= TX_PAD;
                            end else begin
                                tx_state <= TX_CRC;
                            end
                        end
                    end
                end
                TX_PAD: begin
                    if (tx_frame_length < MIN_FRAME_SIZE) begin
                        tx_axis_tdata <= '0;
                        tx_byte_counter <= tx_byte_counter + 16;
                        tx_frame_length <= tx_frame_length + 16;
                    end else begin
                        tx_state <= TX_CRC;
                    end
                end
                TX_CRC: begin
                    tx_axis_tlast <= 1'b1;
                    tx_axis_tdata[31:0] <= tx_crc;
                    tx_state <= TX_IPG;
                    ipg_counter <= 8'd12;
                end
                TX_IPG: begin
                    tx_axis_tvalid <= 1'b0;
                    tx_axis_tlast <= 1'b0;
                    if (ipg_counter > 0) begin
                        ipg_counter <= ipg_counter - 1;
                    end else begin
                        ipg_ready <= 1'b1;
                        tx_state <= TX_IDLE;
                    end
                end
                TX_COLLISION: begin
                    if (duplex_mode == 1'b0) begin
                        tx_underrun <= 1'b1;
                        tx_error_count <= tx_error_count + 1;
                    end
                    tx_state <= TX_IDLE;
                end
            endcase
        end
    end

    // RX State Machine
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            rx_state <= RX_IDLE;
            rx_enable <= 1'b0;
            rx_byte_counter <= '0;
            rx_axis_tready <= 1'b1;
            rx_axis_tvalid <= 1'b0;
            rx_axis_tlast <= 1'b0;
            rx_axis_tdata <= '0;
            rx_axis_tuser <= '0;
        end else begin
            case (rx_state)
                RX_IDLE: begin
                    if (mac_rx_dv && (mac_rx_data == 8'h55)) begin
                        rx_state <= RX_PREAMBLE;
                        rx_byte_counter <= '0;
                    end
                end
                RX_PREAMBLE: begin
                    if (mac_rx_dv) begin
                        rx_byte_counter <= rx_byte_counter + 1;
                        if (mac_rx_data == 8'hD5) begin
                            rx_state <= RX_SFD;
                        end else if (rx_byte_counter > 8) begin
                            rx_state <= RX_DROP;
                        end
                    end else begin
                        rx_state <= RX_IDLE;
                    end
                end
                RX_SFD: begin
                    rx_state <= RX_DATA;
                    rx_byte_counter <= '0;
                end
                RX_DATA: begin
                    if (mac_rx_dv) begin
                        rx_axis_tdata[rx_byte_counter*8+:8] <= mac_rx_data;
                        rx_byte_counter <= rx_byte_counter + 1;
                        if (mac_rx_data == 8'hD5 && rx_byte_counter == 0) begin
                            rx_state <= RX_DROP;
                        end
                    end else begin
                        rx_frame_length <= rx_byte_counter;
                        if (rx_byte_counter < MIN_FRAME_SIZE) begin
                            rx_state <= RX_DROP;
                            rx_error_count <= rx_error_count + 1;
                        end else begin
                            rx_state <= RX_CRC;
                        end
                    end
                end
                RX_CRC: begin
                    if (crc_error) begin
                        rx_axis_tuser[0] <= 1'b1;
                        rx_error_count <= rx_error_count + 1;
                    end
                    rx_axis_tvalid <= 1'b1;
                    rx_axis_tlast <= 1'b1;
                    rx_state <= RX_IDLE;
                end
                RX_DROP: begin
                    rx_axis_tuser[1] <= 1'b1;
                    rx_state <= RX_IDLE;
                end
                RX_PAUSE: begin
                    if (pause_timer > 0) begin
                        pause_timer <= pause_timer - 1;
                    end else begin
                        rx_state <= RX_IDLE;
                    end
                end
            endcase
        end
    end

    // CRC Generation (Ethernet FCS)
    function [31:0] crc32_byte(input [7:0] data, input [31:0] crc);
        integer i;
        begin
            crc32_byte = crc;
            for (i = 0; i < 8; i++) begin
                if (crc32_byte[31] ^ data[i]) begin
                    crc32_byte = {crc32_byte[30:0], 1'b0} ^ 32'h04C11DB7;
                end else begin
                    crc32_byte = {crc32_byte[30:0], 1'b0};
                end
            end
        end
    endfunction

    // Statistics Update
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            stats_tx_bytes <= '0;
            stats_rx_bytes <= '0;
            stats_tx_pkts <= '0;
            stats_rx_pkts <= '0;
            stats_tx_errors <= '0;
            stats_rx_errors <= '0;
        end else begin
            if (tx_axis_tlast && tx_axis_tvalid && tx_axis_tready) begin
                stats_tx_bytes <= stats_tx_bytes + tx_frame_length;
                stats_tx_pkts <= stats_tx_pkts + 1;
            end
            if (rx_axis_tlast && rx_axis_tvalid && rx_axis_tready) begin
                stats_rx_bytes <= stats_rx_bytes + rx_frame_length;
                stats_rx_pkts <= stats_rx_pkts + 1;
            end
            if (tx_underrun) begin
                stats_tx_errors <= stats_tx_errors + 1;
            end
            if (crc_error) begin
                stats_rx_errors <= stats_rx_errors + 1;
            end
        end
    end

    // Interrupt Generation
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            eth_intr <= '0;
        end else begin
            eth_intr[0] <= (tx_axis_tlast && tx_axis_tvalid);
            eth_intr[1] <= (rx_axis_tlast && rx_axis_tvalid);
            eth_intr[2] <= (crc_error || rx_frame_error);
            eth_intr[3] <= !link_status;
            eth_intr[4] <= (pause_timer > 0);
            eth_intr[7:5] <= '0;
        end
    end

    // Pause Frame Handling
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            pause_timer <= '0;
        end else begin
            if (mac_rx_dv && (mac_rx_data == 8'h88) && (mac_rx_data == 8'h08)) begin
                if (mac_rx_data == 8'h01) begin
                    pause_timer <= {mac_rx_data, 8'h00};
                end
            end
        end
    end

endmodule
