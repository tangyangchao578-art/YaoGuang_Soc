//-----------------------------------------------------------------------------
// File: pcie_transaction_layer.sv
// Description: PCIe Transaction Layer (TLP/DLLP Processing)
// Author: YaoGuang SoC Team
// Date: 2026-01-19
//-----------------------------------------------------------------------------

`timescale 1ps/1ps

module pcie_transaction_layer #(
    parameter AXI_DATA_WIDTH = 256,
    parameter AXI_ADDR_WIDTH = 48,
    parameter MAX_PAYLOAD_SIZE = 256,
    parameter MAX_READ_REQ_SIZE = 4096,
    parameter NUM_VF = 64,
    parameter NUM_PF = 8
) (
    input  logic                                clk,
    input  logic                                rst_n,
    output logic [AXI_ADDR_WIDTH-1:0]           axi_m_araddr,
    output logic [2:0]                          axi_m_arprot,
    output logic                                axi_m_arvalid,
    input  logic                                axi_m_arready,
    output logic [AXI_ADDR_WIDTH-1:0]           axi_m_awaddr,
    output logic [2:0]                          axi_m_awprot,
    output logic                                axi_m_awvalid,
    input  logic                                axi_m_awready,
    output logic [AXI_DATA_WIDTH-1:0]           axi_m_wdata,
    output logic [(AXI_DATA_WIDTH/8)-1:0]       axi_m_wstrb,
    output logic                                axi_m_wlast,
    output logic                                axi_m_wvalid,
    input  logic                                axi_m_wready,
    input  logic [1:0]                          axi_m_bresp,
    input  logic                                axi_m_bvalid,
    output logic                                axi_m_bready,
    input  logic [AXI_DATA_WIDTH-1:0]           axi_m_rdata,
    input  logic [1:0]                          axi_m_rresp,
    input  logic                                axi_m_rvalid,
    output logic                                axi_m_rready,
    input  logic [AXI_ADDR_WIDTH-1:0]           axi_s_araddr,
    input  logic [2:0]                          axi_s_arprot,
    input  logic                                axi_s_arvalid,
    output logic                                axi_s_arready,
    input  logic [AXI_ADDR_WIDTH-1:0]           axi_s_awaddr,
    input  logic [2:0]                          axi_s_awprot,
    input  logic                                axi_s_awvalid,
    output logic                                axi_s_awready,
    input  logic [AXI_DATA_WIDTH-1:0]           axi_s_wdata,
    input  logic [(AXI_DATA_WIDTH/8)-1:0]       axi_s_wstrb,
    input  logic                                axi_s_wlast,
    input  logic                                axi_s_wvalid,
    output logic                                axi_s_wready,
    output logic [1:0]                          axi_s_bresp,
    output logic                                axi_s_bvalid,
    input  logic                                axi_s_bready,
    output logic [AXI_DATA_WIDTH-1:0]           axi_s_rdata,
    output logic [1:0]                          axi_s_rresp,
    output logic                                axi_s_rvalid,
    input  logic                                axi_s_rready,
    input  logic [15:0]                         device_id,
    input  logic [15:0]                         vendor_id,
    input  logic [7:0]                          revision_id,
    input  logic [2:0]                          class_code,
    output logic [5:0]                          interrupt_out,
    output logic                                interrupt_pending,
    input  logic                                msix_enable,
    input  logic                                msi_enable,
    output logic [7:0]                          cfg_bus_number,
    output logic [2:0]                          cfg_device_number,
    output logic [4:0]                          cfg_function_number,
    output logic [15:0]                         cfg_command,
    output logic [15:0]                         cfg_status,
    output logic [11:0]                         cfg_dcommand,
    output logic [11:0]                         cfg_lcommand,
    input  logic                                dll_tx_seq_num,
    input  logic                                dll_rx_seq_num,
    output logic                                dll_tx_ack,
    output logic                                dll_rx_ack,
    output logic [15:0]                         dll_tx_credits,
    input  logic [15:0]                         dll_rx_credits,
    output logic [AXI_DATA_WIDTH-1:0]           tl_tx_data,
    input  logic [AXI_DATA_WIDTH-1:0]           tl_rx_data,
    output logic                                tl_tx_valid,
    input  logic                                tl_tx_ready,
    input  logic                                tl_rx_valid,
    output logic                                tl_rx_ready,
    output logic [31:0]                         tl_tx_hdr,
    input  logic [31:0]                         tl_rx_hdr,
    output logic                                tl_tx_end,
    input  logic                                tl_rx_end,
    output logic                                error_correctable,
    output logic                                error_non_fatal,
    output logic                                error_fatal
);

    localparam TLP_HEADER_SIZE = 32;
    localparam MAX_TLP_SIZE = 1024;

    // TLP Types
    typedef enum logic [7:0] {
        TLP_MEM_READ_32 = 8'b00_000_000,
        TLP_MEM_READ_64 = 8'b01_000_000,
        TLP_MEM_WRITE_32 = 8'b01_000_010,
        TLP_MEM_WRITE_64 = 8'b01_000_011,
        TLP_IO_READ = 8'b00_000_010,
        TLP_IO_WRITE = 8'b00_000_011,
        TLP_CFG_READ_0 = 8'b00_001_000,
        TLP_CFG_WRITE_0 = 8'b00_001_010,
        TLP_CFG_READ_1 = 8'b00_001_001,
        TLP_CFG_WRITE_1 = 8'b00_001_011,
        TLP_MSG = 8'b10_000_000,
        TLP_CPL = 8'b00_001_010,
        TLP_CPLD = 8'b00_001_010
    } tlp_type_t;

    // TLP Format
    typedef enum logic [2:0] {
        FMT_3DW = 3'b000,
        FMT_4DW = 3'b001,
        FMT_3DW_DATA = 3'b010,
        FMT_4DW_DATA = 3'b011
    } tlp_fmt_t;

    // Internal Registers
    logic [9:0]                                  tx_queue_head;
    logic [9:0]                                  tx_queue_tail;
    logic [9:0]                                  rx_queue_head;
    logic [9:0]                                  rx_queue_tail;
    logic [31:0]                                 tlp_header_fifo [0:31];
    logic [AXI_DATA_WIDTH-1:0]                   tlp_data_fifo [0:31];
    logic                                        tlp_header_valid;
    logic [5:0]                                  tx_credits_avail;
    logic                                        rx_credits_avail;

    // Configuration Space
    logic [15:0]                                 cfg_dev_cap;
    logic [15:0]                                 cfg_dev_ctrl;
    logic [15:0]                                 cfg_link_cap;
    logic [15:0]                                 cfg_link_ctrl;
    logic [255:0]                                cfg_ext_cap;
    logic [15:0]                                 cfg_aer_cap;
    logic [15:0]                                 cfg_aer_ctrl;

    // AXI Request FIFOs
    logic [AXI_ADDR_WIDTH-1:0]                   axi_araddr_fifo [0:15];
    logic [7:0]                                  axi_arid_fifo [0:15];
    logic [7:0]                                  axi_arid_reg;
    logic                                        axi_arvalid_reg;
    logic [AXI_ADDR_WIDTH-1:0]                   axi_awaddr_fifo [0:15];
    logic [7:0]                                  axi_awid_fifo [0:15];
    logic                                        axi_awvalid_reg;
    logic [AXI_DATA_WIDTH-1:0]                   axi_wdata_fifo [0:63];
    logic [(AXI_DATA_WIDTH/8)-1:0]               axi_wstrb_fifo [0:63];
    logic                                        axi_wlast_fifo [0:63];
    logic                                        axi_wvalid_reg;

    // Completion Tracking
    logic [15:0]                                 completer_id;
    logic [15:0]                                 requester_id;
    logic [11:0]                                 tag_alloc;
    logic [11:0]                                 tag_dealloc;
    logic [11:0]                                 outstanding_tags;

    // TLP Transmit State Machine
    typedef enum logic [3:0] {
        TX_IDLE,
        TX_HDR_FMT,
        TX_ADDR,
        TX_DATA,
        TX_CPL,
        TX_WAIT_CREDIT
    } tx_state_t;

    tx_state_t tx_state;

    // TLP Receive State Machine
    typedef enum logic [3:0] {
        RX_IDLE,
        RX_HDR_FMT,
        RX_ADDR,
        RX_DATA,
        RX_CPL,
        RX_ACK
    } rx_state_t;

    rx_state_t rx_state;

    // AXI Master Write Channel
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            axi_m_awvalid <= 1'b0;
            axi_m_awaddr <= '0;
            axi_m_awprot <= '0;
            axi_m_wvalid <= 1'b0;
            axi_m_wdata <= '0;
            axi_m_wstrb <= '0;
            axi_m_wlast <= 1'b0;
            axi_m_bready <= 1'b1;
            tx_state <= TX_IDLE;
        end else begin
            case (tx_state)
                TX_IDLE: begin
                    if (axi_s_awvalid && axi_s_awready) begin
                        axi_m_awaddr <= axi_s_awaddr;
                        axi_m_awprot <= axi_s_awprot;
                        axi_m_awvalid <= 1'b1;
                        axi_awaddr_fifo[tx_queue_tail] <= axi_s_awaddr;
                        tx_queue_tail <= tx_queue_tail + 1;
                        tx_state <= TX_DATA;
                    end
                end
                TX_DATA: begin
                    axi_m_awvalid <= 1'b0;
                    if (axi_s_wvalid && axi_s_wready) begin
                        axi_m_wdata <= axi_s_wdata;
                        axi_m_wstrb <= axi_s_wstrb;
                        axi_m_wlast <= axi_s_wlast;
                        axi_m_wvalid <= 1'b1;
                        if (axi_s_wlast) begin
                            tl_tx_hdr <= build_tlp_header(TLP_MEM_WRITE_64, axi_s_awaddr, axi_s_wdata[AXI_DATA_WIDTH-1:0]);
                            tl_tx_valid <= 1'b1;
                            tx_state <= TX_WAIT_CREDIT;
                        end
                    end
                end
                TX_WAIT_CREDIT: begin
                    axi_m_wvalid <= 1'b0;
                    axi_m_wlast <= 1'b0;
                    if (dll_tx_ack) begin
                        tl_tx_valid <= 1'b0;
                        tx_state <= TX_IDLE;
                    end
                end
            endcase
        end
    end

    // AXI Master Read Channel
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            axi_m_arvalid <= 1'b0;
            axi_m_araddr <= '0;
            axi_m_arprot <= '0;
            axi_m_rready <= 1'b1;
            rx_state <= RX_IDLE;
        end else begin
            case (rx_state)
                RX_IDLE: begin
                    if (axi_s_arvalid && axi_s_arready) begin
                        axi_m_araddr <= axi_s_araddr;
                        axi_m_arprot <= axi_s_arprot;
                        axi_m_arvalid <= 1'b1;
                        tag_alloc <= tag_alloc + 1;
                        tl_tx_hdr <= build_tlp_header(TLP_MEM_READ_64, axi_s_araddr, '0);
                        tl_tx_valid <= 1'b1;
                        rx_state <= RX_CPL;
                    end
                end
                RX_CPL: begin
                    axi_m_arvalid <= 1'b0;
                    if (tl_rx_valid && tl_rx_ready) begin
                        if (tl_rx_hdr[7:0] == TLP_CPLD) begin
                            axi_s_rdata <= tl_rx_data;
                            axi_s_rresp <= '0;
                            axi_s_rvalid <= 1'b1;
                            rx_state <= RX_IDLE;
                        end
                    end
                end
            endcase
        end
    end

    // AXI Slave Interface
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            axi_s_arready <= 1'b1;
            axi_s_awready <= 1'b1;
            axi_s_wready <= 1'b0;
            axi_s_bvalid <= 1'b0;
            axi_s_bresp <= '0;
            axi_s_rvalid <= 1'b0;
            axi_s_rdata <= '0;
            axi_s_rresp <= '0;
        end else begin
            axi_s_arready <= !axi_s_arvalid;
            axi_s_awready <= !axi_s_awvalid;
            axi_s_wready <= (axi_s_awvalid && axi_s_awready) && !axi_s_wvalid;

            if (axi_s_arvalid && axi_s_arready) begin
                axi_s_arready <= 1'b0;
            end

            if (axi_s_awvalid && axi_s_awready) begin
                axi_s_awready <= 1'b0;
            end

            if (axi_s_wvalid && axi_s_wready) begin
                axi_s_wready <= 1'b0;
                if (axi_s_wlast) begin
                    axi_s_bvalid <= 1'b1;
                    axi_s_bresp <= axi_m_bresp;
                end
            end

            if (axi_s_bvalid && axi_s_bready) begin
                axi_s_bvalid <= 1'b0;
            end
        end
    end

    // TLP Header Construction
    function [31:0] build_tlp_header(
        input tlp_type_t tlp_type,
        input [AXI_ADDR_WIDTH-1:0] addr,
        input [AXI_DATA_WIDTH-1:0] data
    );
        build_tlp_header = {
            3'b000,                                     // Reserved
            tlp_type,                                   // Type
            2'b00,                                      // Reserved
            1'b0,                                       // Attr[0]
            2'b00,                                      // TC
            1'b0,                                       // Reserved
            1'b0,                                       // TH
            1'b0,                                       // TD
            1'b0,                                       // EP
            2'b00,                                      // Attr[2:1]
            8'd4                                        // Length
        };
    endfunction

    // Configuration Space Access
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            cfg_command <= 16'h0007;
            cfg_status <= 16'h0010;
            cfg_dev_cap <= 16'h0010;
            cfg_dev_ctrl <= 16'h0000;
            cfg_link_cap <= 16'h0303;
            cfg_link_ctrl <= 16'h0000;
        end else begin
            // Device Control
            if (axi_s_awvalid && (axi_s_awaddr[11:8] == 4'h4)) begin
                cfg_command[15:0] <= axi_s_wdata[15:0];
            end
            // Link Status
            cfg_status[18] <= link_up;
            cfg_status[19] <= slot_power_limit;
        end
    end

    // MSI/MSI-X Interrupt Generation
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            interrupt_out <= '0;
            interrupt_pending <= 1'b0;
        end else begin
            if (msix_enable) begin
                if (msix_vector_pending) begin
                    interrupt_out <= msix_vector;
                    interrupt_pending <= 1'b1;
                end else begin
                    interrupt_pending <= 1'b0;
                end
            end else if (msi_enable) begin
                if (msi_pending) begin
                    interrupt_out <= msi_vector;
                    interrupt_pending <= 1'b1;
                end else begin
                    interrupt_pending <= 1'b0;
                end
            end
        end
    end

    // Error Handling
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            error_correctable <= 1'b0;
            error_non_fatal <= 1'b0;
            error_fatal <= 1'b0;
        end else begin
            error_correctable <= ecc_error_corrected;
            error_non_fatal <= (tlp_poisoned || tl_timeout);
            error_fatal <= (link_down || tl_uncorrectable);
        end
    end

    // Tag Management
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            outstanding_tags <= '0;
            tag_alloc <= '0;
        end else begin
            if (axi_s_arvalid && axi_s_arready) begin
                outstanding_tags <= outstanding_tags + 1;
            end
            if (tl_rx_valid && (tl_rx_hdr[7:0] == TLP_CPLD)) begin
                outstanding_tags <= outstanding_tags - 1;
            end
        end
    end

    // Flow Control
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            dll_tx_credits <= 16'd256;
            tx_credits_avail <= 8'd128;
        end else begin
            dll_tx_credits <= dll_rx_credits;
            tx_credits_avail <= dll_rx_credits[7:0];
        end
    end

endmodule
