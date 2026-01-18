//-----------------------------------------------------------------------------
// File: usb_host_device_controller.sv
// Description: USB Host/Device Controller with xHCI Support
// Author: YaoGuang SoC Team
// Date: 2026-01-19
//-----------------------------------------------------------------------------

`timescale 1ps/1ps

module usb_host_device_controller #(
    parameter PORT_ID = 0,
    parameter AXI_DATA_WIDTH = 128,
    parameter MAX_EPS = 16
) (
    input  logic                                clk_sys,
    input  logic                                clk_phy,
    input  logic                                rst_n_sys,
    input  logic                                rst_n_phy,
    input  logic [15:0]                         dev_addr,
    input  logic                                device_configured,
    output logic                                port_connected,
    output logic                                port_enabled,
    output logic [1:0]                          port_speed,
    input  logic                                port_overcurrent,
    input  logic [AXI_ADDR_WIDTH-1:0]           s_axibus_awaddr,
    input  logic [3:0]                          s_axibus_awid,
    input  logic [7:0]                          s_axibus_awlen,
    input  logic [2:0]                          s_axibus_awsize,
    input  logic [1:0]                          s_axibus_awburst,
    input  logic                                s_axibus_awvalid,
    output logic                                s_axibus_awready,
    input  logic [AXI_DATA_WIDTH-1:0]           s_axibus_wdata,
    input  logic [(AXI_DATA_WIDTH/8)-1:0]       s_axibus_wstrb,
    input  logic                                s_axibus_wlast,
    input  logic                                s_axibus_wvalid,
    output logic                                s_axibus_wready,
    output logic [1:0]                          s_axibus_bresp,
    output logic                                s_axibus_bvalid,
    input  logic                                s_axibus_bready,
    input  logic [AXI_ADDR_WIDTH-1:0]           s_axibus_araddr,
    input  logic [3:0]                          s_axibus_arid,
    input  logic [7:0]                          s_axibus_arlen,
    input  logic [2:0]                          s_axibus_arsize,
    input  logic [1:0]                          s_axibus_arburst,
    input  logic                                s_axibus_arvalid,
    output logic                                s_axibus_arready,
    output logic [AXI_DATA_WIDTH-1:0]           s_axibus_rdata,
    output logic [1:0]                          s_axibus_rresp,
    output logic                                s_axibus_rlast,
    output logic                                s_axibus_rvalid,
    input  logic                                s_axibus_rready,
    input  logic                                usb2_rx_dp,
    input  logic                                usb2_rx_dn,
    output logic                                usb2_tx_dp,
    output logic                                usb2_tx_dn,
    output logic                                usb2_tx_oe,
    input  logic                                usb2_rx_valid,
    output logic                                usb3_tx_p,
    output logic                                usb3_tx_n,
    input  logic                                usb3_rx_p,
    input  logic                                usb3_rx_n,
    output logic                                usb3_tx_elec_idle,
    input  logic [9:0]                          usb3_rx_data,
    input  logic                                usb3_rx_valid,
    input  logic                                usb3_rx_header_valid,
    output logic [3:0]                          usb_intr,
    input  logic                                runtime_suspend,
    output logic                                runtime_resume,
    input  logic                                global_power_enable
);

    localparam EP_TYPE_CONTROL = 2'b00;
    localparam EP_TYPE_ISO = 2'b01;
    localparam EP_TYPE_BULK = 2'b10;
    localparam EP_TYPE_INT = 2'b11;

    // xHCI Registers
    logic [31:0]                                cap_length;
    logic [31:0]                                hci_version;
    logic [31:0]                                hcs_params1;
    logic [31:0]                                hcs_params2;
    logic [31:0]                                hcs_params3;
    logic [31:0]                                hcc_params1;
    logic [31:0]                                hcc_params2;
    logic [63:0]                                dba_offset;
    logic [63:0]                                dbc_offset;

    // Operational Registers
    logic [31:0]                                usb_cmd;
    logic [31:0]                                usb_sts;
    logic [31:0]                                page_size;
    logic [31:0]                                dn_ctrl;
    logic [31:0]                                crcr_lo;
    logic [31:0]                                crcr_hi;
    logic [31:0]                                dcbaap_lo;
    logic [31:0]                                dcbaap_hi;
    logic [31:0]                                config;

    // Doorbell Registers
    logic [31:0]                                doorbell [0:15];
    logic [31:0]                                doorbell_arb;

    // Runtime Registers
    logic [31:0]                                mfindex;
    logic [31:0]                                ir_lo [0:7];
    logic [31:0]                                ir_hi [0:7];

    // Endpoint Context
    logic [31:0]                                ep_ctx [0:MAX_EPS-1];
    logic [31:0]                                input_ctx [0:31];

    // TRB Ring
    logic [63:0]                                trb_ring_base [0:255];
    logic [8:0]                                 trb_dequeue_ptr [0:15];
    logic [8:0]                                 trb_enqueue_ptr [0:15];
    logic                                        trb_ring_full [0:15];

    // Transfer State Machine
    typedef enum logic [3:0] {
        XFER_IDLE,
        XFER_SETUP,
        XFER_DATA,
        XFER_STATUS,
        XFER_COMPLETE,
        XFER_HALTED,
        XFER_ERROR
    } xfer_state_t;

    xfer_state_t xfer_state [0:MAX_EPS-1];

    // Packet Buffer
    logic [7:0]                                 rx_buf [0:1023];
    logic [7:0]                                 tx_buf [0:1023];
    logic [9:0]                                 rx_buf_wr_ptr;
    logic [9:0]                                 rx_buf_rd_ptr;
    logic [9:0]                                 tx_buf_wr_ptr;
    logic [9:0]                                 tx_buf_rd_ptr;

    // USB 2.0 NRZI Decoder
    logic                                        nrzi_dec_out;
    logic                                        nrzi_dec_valid;
    logic                                        bit_stuff_decode;
    logic                                        bit_stuff_error;

    // USB 3.2 Scrambler/Descrambler
    logic [15:0]                                lfsr_state;
    logic                                        lfsr_enable;

    // USB 3.2 8b/10b Encoder/Decoder
    logic [9:0]                                 enc_data;
    logic                                        enc_kchar;
    logic                                        enc_valid;
    logic [9:0]                                 dec_data;
    logic                                        dec_kchar;
    logic                                        dec_valid;
    logic                                        dec_error;

    // Address and Endpoint Decoding
    logic [3:0]                                 target_ep;
    logic [1:0]                                 ep_type;
    logic [2:0]                                 ep_state;
    logic                                        ep_enabled;
    logic                                        ep_stalled;
    logic [15:0]                                 ep_max_pkt_size;
    logic [15:0]                                 ep_interval;

    // AXI Slave Interface
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            s_axibus_awready <= 1'b1;
            s_axibus_wready <= 1'b0;
            s_axibus_bvalid <= 1'b0;
            s_axibus_bresp <= '0;
            s_axibus_arready <= 1'b1;
            s_axibus_rvalid <= 1'b0;
            s_axibus_rdata <= '0;
            s_axibus_rresp <= '0;
            s_axibus_rlast <= 1'b1;
        end else begin
            s_axibus_awready <= !s_axibus_awvalid;
            s_axibus_wready <= (s_axibus_awvalid && s_axibus_awready) && !s_axibus_wvalid;

            if (s_axibus_awvalid && s_axibus_awready) begin
                s_axibus_awready <= 1'b0;
                s_axibus_wready <= 1'b1;
            end

            if (s_axibus_wvalid && s_axibus_wready) begin
                s_axibus_wready <= 1'b0;
                if (s_axibus_wlast) begin
                    s_axibus_bvalid <= 1'b1;
                    s_axibus_bresp <= '0;
                end
            end

            if (s_axibus_bvalid && s_axibus_bready) begin
                s_axibus_bvalid <= 1'b0;
            end

            s_axibus_arready <= !s_axibus_arvalid;

            if (s_axibus_arvalid && s_axibus_arready) begin
                s_axibus_arready <= 1'b0;
                case (s_axibus_araddr[11:8])
                    4'h0: s_axibus_rdata <= cap_length;
                    4'h1: s_axibus_rdata <= hci_version;
                    4'h2: s_axibus_rdata <= hcs_params1;
                    4'h3: s_axibus_rdata <= hcs_params2;
                    4'h4: s_axibus_rdata <= hcs_params3;
                    4'h5: s_axibus_rdata <= hcc_params1;
                    4'h6: s_axibus_rdata <= hcc_params2;
                    4'h10: s_axibus_rdata <= usb_cmd;
                    4'h11: s_axibus_rdata <= usb_sts;
                    4'h12: s_axibus_rdata <= page_size;
                    4'h13: s_axibus_rdata <= dn_ctrl;
                    default: s_axibus_rdata <= '0;
                endcase
                s_axibus_rvalid <= 1'b1;
                s_axibus_rlast <= 1'b1;
            end else begin
                s_axibus_rvalid <= 1'b0;
            end
        end
    end

    // xHCI Capability Registers
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            cap_length <= 32'h40;
            hci_version <= 32'h0100;
            hcs_params1 <= 32'h00020005;
            hcs_params2 <= 32'h00000008;
            hcs_params3 <= 32'h00000007;
            hcc_params1 <= 32'h0200001E;
            hcc_params2 <= 32'h00000000;
        end
    end

    // USB Command Register
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            usb_cmd <= '0;
        end else begin
            if (s_axibus_awvalid && (s_axibus_awaddr[11:8] == 4'h10)) begin
                usb_cmd <= s_axibus_wdata[31:0];
            end else begin
                if (usb_cmd[0] && !usb_sts[0]) begin
                    usb_cmd[0] <= 1'b0;
                end
            end
        end
    end

    // USB Status Register
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            usb_sts <= '0;
            port_connected <= 1'b0;
            port_enabled <= 1'b0;
            port_speed <= 2'b00;
        end else begin
            usb_sts[0] <= usb_cmd[0];
            usb_sts[2] <= (usb_sts[2] && !usb_cmd[2]);
            usb_sts[3] <= runtime_suspend;
            usb_sts[4] <= runtime_resume;

            if (phy_connected) begin
                port_connected <= 1'b1;
                port_speed <= detected_speed;
            end
        end
    end

    // Doorbell Handler
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            doorbell_arb <= '0;
            for (int i = 0; i < 16; i++) begin
                doorbell[i] <= '0;
            end
        end else begin
            if (s_axibus_awvalid && (s_axibus_awaddr[11:8] == 4'h20)) begin
                doorbell[s_axibus_awaddr[3:0]] <= s_axibus_wdata[31:0];
            end
            doorbell_arb <= doorbell[0];
            for (int i = 1; i < 16; i++) begin
                doorbell_arb <= doorbell_arb | doorbell[i];
            end
        end
    end

    // TRB Ring Processor
    integer trb_ep_idx;
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            for (int i = 0; i < 16; i++) begin
                trb_dequeue_ptr[i] <= '0;
                trb_enqueue_ptr[i] <= '0;
            end
        end else begin
            for (trb_ep_idx = 0; trb_ep_idx < 16; trb_ep_idx++) begin
                if (doorbell[trb_ep_idx] != 0) begin
                    if (trb_enqueue_ptr[trb_ep_idx] != trb_dequeue_ptr[trb_ep_idx]) begin
                        trb_dequeue_ptr[trb_ep_idx] <= trb_dequeue_ptr[trb_ep_idx] + 1;
                    end
                end
            end
        end
    end

    // USB 2.0 NRZI Decoder
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            nrzi_dec_out <= 1'b0;
            nrzi_dec_valid <= 1'b0;
            bit_stuff_error <= 1'b0;
            rx_buf_wr_ptr <= '0;
        end else begin
            if (usb2_rx_valid) begin
                if (usb2_rx_dp ^ usb2_rx_dn) begin
                    nrzi_dec_out <= !nrzi_dec_out;
                    nrzi_dec_valid <= 1'b1;
                end else begin
                    if (nrzi_dec_out == 1'b1) begin
                        if (bit_stuff_decode == 1'b1) begin
                            bit_stuff_error <= 1'b1;
                        end else begin
                            rx_buf[rx_buf_wr_ptr] <= {nrzi_dec_out, 7'b0};
                            rx_buf_wr_ptr <= rx_buf_wr_ptr + 1;
                        end
                    end
                end
            end
        end
    end

    // USB 2.0 Bit Stuffing
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            bit_stuff_decode <= 1'b0;
            bit_stuff_counter <= 3'b0;
        end else begin
            if (nrzi_dec_valid) begin
                if (bit_stuff_counter == 6) begin
                    bit_stuff_decode <= 1'b1;
                    bit_stuff_counter <= 3'b0;
                end else begin
                    bit_stuff_decode <= 1'b0;
                    if (nrzi_dec_out) begin
                        bit_stuff_counter <= bit_stuff_counter + 1;
                    end else begin
                        bit_stuff_counter <= 3'b0;
                    end
                end
            end
        end
    end

    // USB 3.2 Scrambler
    function [9:0] usb3_scramble(input [9:0] data, input [15:0] lfsr, input enable);
        integer i;
        begin
            if (enable) begin
                for (i = 0; i < 10; i++) begin
                    usb3_scramble[i] = data[i] ^ lfsr[0] ^ lfsr[2];
                end
            end else begin
                usb3_scramble = data;
            end
        end
    endfunction

    // USB 3.2 8b/10b Encoder
    always_ff @(posedge clk_phy or negedge rst_n_phy) begin
        if (!rst_n_phy) begin
            enc_data <= '0;
            enc_kchar <= 1'b0;
            enc_valid <= 1'b0;
        end else begin
            if (usb3_tx_valid) begin
                case (tx_char)
                    8'b00111101: enc_data <= 10'b0100111010; // K28.5
                    8'b00111110: enc_data <= 10'b0010111010; // K28.6
                    8'b00111111: enc_data <= 10'b0011111010; // K28.7
                    default: enc_data <= encode_8b10b(tx_char);
                endcase
                enc_kchar <= is_k_char(tx_char);
                enc_valid <= 1'b1;
            end else begin
                enc_valid <= 1'b0;
            end
        end
    endfunction

    // Interrupt Generation
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            usb_intr <= '0;
        end else begin
            usb_intr[0] <= usb_sts[0];
            usb_intr[1] <= usb_sts[1];
            usb_intr[2] <= usb_sts[2];
            usb_intr[3] <= |port_event;
        end
    end

    // Port Event Handler
    logic [3:0]                                 port_event;
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            port_event <= '0;
        end else begin
            if (phy_connected && !port_connected) begin
                port_event[0] <= 1'b1;
            end
            if (port_disconnected) begin
                port_event[1] <= 1'b1;
            end
            if (port_overcurrent) begin
                port_event[2] <= 1'b1;
            end
            if (port_warm_reset) begin
                port_event[3] <= 1'b1;
            end
        end
    end

endmodule
