//-----------------------------------------------------------------------------
// File: frame_preprocessor.sv
// Description: Ethernet Frame Preprocessor (TSN/VLAN/TSM)
// Author: YaoGuang SoC Team
// Date: 2026-01-19
//-----------------------------------------------------------------------------

`timescale 1ps/1ps

module frame_preprocessor #(
    parameter PORT_ID = 0
) (
    input  logic                                clk_sys,
    input  logic                                rst_n_sys,
    input  logic                                tx_axis_tvalid,
    input  logic                                tx_axis_tlast,
    input  logic [6:0]                          tx_axis_tuser,
    input  logic [127:0]                        tx_axis_tdata,
    output logic                                tx_axis_tready,
    output logic                                rx_axis_tvalid,
    output logic                                rx_axis_tlast,
    output logic [6:0]                          rx_axis_tuser,
    output logic [127:0]                        rx_axis_tdata,
    input  logic                                rx_axis_tready,
    input  logic                                mac_tx_clk,
    input  logic                                mac_rx_clk,
    input  logic                                mac_tx_en,
    input  logic                                mac_tx_err,
    input  logic [7:0]                          mac_tx_data,
    output logic                                mac_rx_dv,
    output logic                                mac_rx_err,
    output logic [7:0]                          mac_rx_data,
    input  logic                                tsn_enable,
    output logic                                vlan_detect,
    output logic                                tsm_insert,
    output logic                                error_frame
);

    localparam MAX_VLAN_TAGS = 2;
    localparam TSM_SIZE = 10;

    typedef enum logic [2:0] {
        PROC_IDLE,
        PROC_PREAMBLE,
        PROC_HEADER,
        PROC_PAYLOAD,
        PROC_FCS,
        PROC_DROP
    } proc_state_t;

    proc_state_t                                 tx_proc_state;
    proc_state_t                                 rx_proc_state;

    logic                                        vlan_enable;
    logic [15:0]                                 vlan_tpid;
    logic [15:0]                                 vlan_pcp;
    logic [15:0]                                 vlan_dei;
    logic [15:0]                                 vlan_vid;
    logic [2:0]                                  vlan_tag_count;

    logic                                        tsm_enable;
    logic [79:0]                                 tsm_value;
    logic                                        frame_preemption_enable;
    logic [3:0]                                  tx_queue_select;
    logic [3:0]                                  rx_queue_select;
    logic                                        cut_through_enable;
    logic                                        store_forward_enable;

    logic [47:0]                                 local_time;
    logic                                        tsm_valid;
    logic [79:0]                                 tsm_tx_timestamp;
    logic [79:0]                                 tsm_rx_timestamp;

    logic [31:0]                                 rx_ip_checksum;
    logic [31:0]                                 rx_tcp_checksum;
    logic                                        checksum_error;

    logic                                        frame_too_long;
    logic                                        frame_too_short;
    logic                                        jabber_detect;
    logic                                        crc_error;

    logic [15:0]                                 vlan_frames;
    logic [15:0]                                 qav_frames;
    logic [15:0]                                 preemption_frames;

    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            tx_proc_state <= PROC_IDLE;
            tx_axis_tready <= 1'b1;
            tx_axis_tvalid <= 1'b0;
            tx_axis_tlast <= 1'b0;
            tx_axis_tdata <= '0;
            tx_axis_tuser <= '0;
        end else begin
            case (tx_proc_state)
                PROC_IDLE: begin
                    if (tx_axis_tvalid) begin
                        tx_proc_state <= PROC_PREAMBLE;
                    end
                end
                PROC_PREAMBLE: begin
                    if (tx_axis_tvalid && tx_axis_tready) begin
                        tx_axis_tdata <= {tx_axis_tdata[119:0], 8'h55};
                        if (tx_axis_tlast) begin
                            tx_axis_tlast <= 1'b0;
                            tx_proc_state <= PROC_HEADER;
                        end
                    end
                end
                PROC_HEADER: begin
                    if (tx_axis_tvalid && tx_axis_tready) begin
                        if (vlan_enable && (tx_axis_tdata[79:64] == vlan_tpid)) begin
                            vlan_detect <= 1'b1;
                            tx_axis_tdata[79:64] <= {vlan_pcp, vlan_dei, vlan_vid};
                        end
                        tx_proc_state <= PROC_PAYLOAD;
                    end
                end
                PROC_PAYLOAD: begin
                    if (tx_axis_tvalid && tx_axis_tready) begin
                        if (tsm_enable && tx_axis_tlast) begin
                            tsm_insert <= 1'b1;
                            tx_axis_tdata <= {tsm_value, 118'b0};
                        end
                        if (tx_axis_tlast) begin
                            tx_proc_state <= PROC_FCS;
                        end
                    end
                end
                PROC_FCS: begin
                    tx_axis_tlast <= 1'b1;
                    tx_axis_tdata[31:0] <= generate_fcs(tx_axis_tdata[127:32]);
                    tx_proc_state <= PROC_IDLE;
                end
                PROC_DROP: begin
                    error_frame <= 1'b1;
                    tx_proc_state <= PROC_IDLE;
                end
            endcase
        end
    end

    always_ff @(posedge mac_rx_clk or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            rx_proc_state <= PROC_IDLE;
            rx_axis_tvalid <= 1'b0;
            rx_axis_tlast <= 1'b0;
            rx_axis_tdata <= '0;
            rx_axis_tuser <= '0;
            mac_rx_dv <= 1'b0;
            mac_rx_err <= 1'b0;
            mac_rx_data <= '0;
        end else begin
            case (rx_proc_state)
                PROC_IDLE: begin
                    if (mac_rx_dv && (mac_rx_data == 8'h55)) begin
                        rx_proc_state <= PROC_PREAMBLE;
                    end
                end
                PROC_PREAMBLE: begin
                    if (mac_rx_dv) begin
                        rx_axis_tdata <= {rx_axis_tdata[119:0], mac_rx_data};
                        if (mac_rx_data == 8'hD5) begin
                            rx_proc_state <= PROC_HEADER;
                        end
                    end else begin
                        rx_proc_state <= PROC_IDLE;
                    end
                end
                PROC_HEADER: begin
                    if (mac_rx_dv) begin
                        rx_axis_tdata <= {rx_axis_tdata[119:0], mac_rx_data};
                        if (rx_axis_tdata[79:64] == 16'h8100) begin
                            vlan_detect <= 1'b1;
                            vlan_frames <= vlan_frames + 1;
                        end
                        rx_proc_state <= PROC_PAYLOAD;
                    end
                end
                PROC_PAYLOAD: begin
                    if (mac_rx_dv) begin
                        rx_axis_tdata <= {rx_axis_tdata[119:0], mac_rx_data};
                        rx_axis_tvalid <= 1'b1;
                    end else begin
                        rx_axis_tlast <= 1'b1;
                        rx_axis_tvalid <= 1'b0;
                        if (rx_axis_tdata[127:96] == generate_fcs(rx_axis_tdata[127:32])) begin
                            rx_axis_tuser[0] <= 1'b0;
                        end else begin
                            rx_axis_tuser[0] <= 1'b1;
                            crc_error <= 1'b1;
                        end
                        rx_proc_state <= PROC_IDLE;
                    end
                end
            endcase
        end
    end

    function [31:0] generate_fcs(input [95:0] data);
        integer i;
        reg [31:0] crc;
        begin
            crc = 32'hFFFFFFFF;
            for (i = 0; i < 96; i++) begin
                if (crc[31] ^ data[i]) begin
                    crc = {crc[30:0], 1'b0} ^ 32'h04C11DB7;
                end else begin
                    crc = {crc[30:0], 1'b0};
                end
            end
            generate_fcs = ~crc;
        end
    endfunction

    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            local_time <= '0;
            tsm_valid <= 1'b0;
        end else begin
            local_time <= local_time + 1;
            if (tsm_enable) begin
                if (tx_axis_tlast && tx_axis_tvalid) begin
                    tsm_tx_timestamp <= {local_time, 32'b0};
                    tsm_valid <= 1'b1;
                end
                if (rx_axis_tlast && rx_axis_tvalid) begin
                    tsm_rx_timestamp <= {local_time, 32'b0};
                end
            end
        end
    end

    always_ff @(posedge mac_rx_clk or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            frame_too_long <= 1'b0;
            frame_too_short <= 1'b0;
        end else begin
            if (byte_counter > 1518) begin
                frame_too_long <= 1'b1;
            end
            if (byte_counter < 64) begin
                frame_too_short <= 1'b1;
            end
        end
    end

    always_ff @(posedge mac_rx_clk or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            jabber_detect <= 1'b0;
        end else begin
            if (byte_counter > 16384) begin
                jabber_detect <= 1'b1;
            end
        end
    end

    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            tx_queue_select <= '0;
        end else begin
            if (tsn_enable) begin
                case (local_time[15:12])
                    4'b0000: tx_queue_select <= 4'b0001;
                    4'b0001: tx_queue_select <= 4'b0010;
                    4'b0010: tx_queue_select <= 4'b0100;
                    4'b0011: tx_queue_select <= 4'b1000;
                    default: tx_queue_select <= 4'b1111;
                endcase
            end
        end
    end

endmodule
