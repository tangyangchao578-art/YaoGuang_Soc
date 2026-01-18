//-----------------------------------------------------------------------------
// File: pcie_top.sv
// Description: PCIe Gen4 Controller Top Level
// Author: YaoGuang SoC Team
// Date: 2026-01-19
//-----------------------------------------------------------------------------

`timescale 1ps/1ps

module pcie_top #(
    parameter PCIE lanes_x8 = 8,
    parameter PCIE lanes_x4 = 4,
    parameter MAX_PAYLOAD_SIZE = 256,
    parameter MAX_READ_REQ_SIZE = 4096,
    parameter NUM_VF = 64,
    parameter NUM_PF = 8,
    parameter AXI_DATA_WIDTH = 256,
    parameter AXI_ADDR_WIDTH = 48
) (
    // Clocks and Resets
    input  logic                                clk_sys,
    input  logic                                clk_phy,
    input  logic                                rst_n_sys,
    input  logic                                rst_n_phy,

    // AXI4 Master Interface (to NoC)
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

    // AXI4 Slave Interface (from NoC)
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

    // PCIe PHY Interface
    output logic [lanes_x8-1:0]                 tx_data_p,
    output logic [lanes_x8-1:0]                 tx_data_n,
    input  logic [lanes_x8-1:0]                 rx_data_p,
    input  logic [lanes_x8-1:0]                 rx_data_n,
    output logic                                tx_clk_p,
    output logic                                tx_clk_n,
    input  logic                                rx_clk_p,
    input  logic                                rx_clk_n,
    output logic                                tx_elec_idle,
    input  logic                                phy_ready,
    input  logic                                phy_status,

    // Configuration and Status
    input  logic [15:0]                          device_id,
    input  logic [15:0]                          vendor_id,
    input  logic [7:0]                           revision_id,
    input  logic [2:0]                           class_code,
    output logic [5:0]                           interrupt_out,
    output logic                                 interrupt_pending,
    input  logic                                msix_enable,
    input  logic                                msi_enable,

    // Power Management
    input  logic                                link_training,
    output logic                                link_up,
    output logic [3:0]                          link_width,
    output logic [2:0]                          link_rate,
    input  logic [1:0]                          power_state,
    output logic                                error_correctable,
    output logic                                error_non_fatal,
    output logic                                error_fatal
);

    // Internal Signals
    logic [7:0]                                  cfg_bus_number;
    logic [2:0]                                  cfg_device_number;
    logic [4:0]                                  cfg_function_number;
    logic [15:0]                                 cfg_command;
    logic [15:0]                                 cfg_status;
    logic [11:0]                                 cfg_dcommand;
    logic [11:0]                                 cfg_lcommand;

    // Transaction Layer Signals
    logic [AXI_DATA_WIDTH-1:0]                   tl_tx_data;
    logic [AXI_DATA_WIDTH-1:0]                   tl_rx_data;
    logic                                        tl_tx_valid;
    logic                                        tl_tx_ready;
    logic                                        tl_rx_valid;
    logic                                        tl_rx_ready;
    logic [31:0]                                 tl_tx_hdr;
    logic [31:0]                                 tl_rx_hdr;
    logic                                        tl_tx_end;
    logic                                        tl_rx_end;

    // Data Link Layer Signals
    logic                                        dll_tx_seq_num;
    logic                                        dll_rx_seq_num;
    logic                                        dll_tx_ack;
    logic                                        dll_rx_ack;
    logic [15:0]                                 dll_tx_credits;
    logic [15:0]                                 dll_rx_credits;

    // Physical Layer Signals
    logic [lanes_x8*32-1:0]                      phy_tx_data;
    logic [lanes_x8*32-1:0]                      phy_rx_data;
    logic                                        phy_tx_valid;
    logic                                        phy_rx_valid;
    logic                                        phy_tx_ready;
    logic                                        phy_rx_ready;
    logic [5:0]                                  phy_tx_status;
    logic [5:0]                                  phy_rx_status;

    // Instantiation of sub-modules
    pcie_transaction_layer #(
        .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
        .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .MAX_PAYLOAD_SIZE(MAX_PAYLOAD_SIZE),
        .MAX_READ_REQ_SIZE(MAX_READ_REQ_SIZE),
        .NUM_VF(NUM_VF),
        .NUM_PF(NUM_PF)
    ) u_transaction_layer (
        .clk(clk_sys),
        .rst_n(rst_n_sys),
        .axi_m_araddr(axi_m_araddr),
        .axi_m_arprot(axi_m_arprot),
        .axi_m_arvalid(axi_m_arvalid),
        .axi_m_arready(axi_m_arready),
        .axi_m_awaddr(axi_m_awaddr),
        .axi_m_awprot(axi_m_awprot),
        .axi_m_awvalid(axi_m_awvalid),
        .axi_m_awready(axi_m_awready),
        .axi_m_wdata(axi_m_wdata),
        .axi_m_wstrb(axi_m_wstrb),
        .axi_m_wlast(axi_m_wlast),
        .axi_m_wvalid(axi_m_wvalid),
        .axi_m_wready(axi_m_wready),
        .axi_m_bresp(axi_m_bresp),
        .axi_m_bvalid(axi_m_bvalid),
        .axi_m_bready(axi_m_bready),
        .axi_m_rdata(axi_m_rdata),
        .axi_m_rresp(axi_m_rresp),
        .axi_m_rvalid(axi_m_rvalid),
        .axi_m_rready(axi_m_rready),
        .axi_s_araddr(axi_s_araddr),
        .axi_s_arprot(axi_s_arprot),
        .axi_s_arvalid(axi_s_arvalid),
        .axi_s_arready(axi_s_arready),
        .axi_s_awaddr(axi_s_awaddr),
        .axi_s_awprot(axi_s_awprot),
        .axi_s_awvalid(axi_s_awvalid),
        .axi_s_awready(axi_s_awready),
        .axi_s_wdata(axi_s_wdata),
        .axi_s_wstrb(axi_s_wstrb),
        .axi_s_wlast(axi_s_wlast),
        .axi_s_wvalid(axi_s_wvalid),
        .axi_s_wready(axi_s_wready),
        .axi_s_bresp(axi_s_bresp),
        .axi_s_bvalid(axi_s_bvalid),
        .axi_s_bready(axi_s_bready),
        .axi_s_rdata(axi_s_rdata),
        .axi_s_rresp(axi_s_rresp),
        .axi_s_rvalid(axi_s_rvalid),
        .axi_s_rready(axi_s_rready),
        .device_id(device_id),
        .vendor_id(vendor_id),
        .revision_id(revision_id),
        .class_code(class_code),
        .interrupt_out(interrupt_out),
        .interrupt_pending(interrupt_pending),
        .msix_enable(msix_enable),
        .msi_enable(msi_enable),
        .cfg_bus_number(cfg_bus_number),
        .cfg_device_number(cfg_device_number),
        .cfg_function_number(cfg_function_number),
        .cfg_command(cfg_command),
        .cfg_status(cfg_status),
        .cfg_dcommand(cfg_dcommand),
        .cfg_lcommand(cfg_lcommand),
        .dll_tx_seq_num(dll_tx_seq_num),
        .dll_rx_seq_num(dll_rx_seq_num),
        .dll_tx_ack(dll_tx_ack),
        .dll_rx_ack(dll_rx_ack),
        .dll_tx_credits(dll_tx_credits),
        .dll_rx_credits(dll_rx_credits),
        .tl_tx_data(tl_tx_data),
        .tl_rx_data(tl_rx_data),
        .tl_tx_valid(tl_tx_valid),
        .tl_tx_ready(tl_tx_ready),
        .tl_rx_valid(tl_rx_valid),
        .tl_rx_ready(tl_rx_ready),
        .tl_tx_hdr(tl_tx_hdr),
        .tl_rx_hdr(tl_rx_hdr),
        .tl_tx_end(tl_tx_end),
        .tl_rx_end(tl_rx_end),
        .error_correctable(error_correctable),
        .error_non_fatal(error_non_fatal),
        .error_fatal(error_fatal)
    );

    pcie_data_link_layer #(
        .LANES(lanes_x8)
    ) u_data_link_layer (
        .clk_sys(clk_sys),
        .clk_phy(clk_phy),
        .rst_n_sys(rst_n_sys),
        .rst_n_phy(rst_n_phy),
        .tl_tx_data(tl_tx_data),
        .tl_rx_data(tl_rx_data),
        .tl_tx_valid(tl_tx_valid),
        .tl_tx_ready(tl_tx_ready),
        .tl_rx_valid(tl_rx_valid),
        .tl_rx_ready(tl_rx_ready),
        .tl_tx_hdr(tl_tx_hdr),
        .tl_rx_hdr(tl_rx_hdr),
        .tl_tx_end(tl_tx_end),
        .tl_rx_end(tl_rx_end),
        .dll_tx_seq_num(dll_tx_seq_num),
        .dll_rx_seq_num(dll_rx_seq_num),
        .dll_tx_ack(dll_tx_ack),
        .dll_rx_ack(dll_rx_ack),
        .dll_tx_credits(dll_tx_credits),
        .dll_rx_credits(dll_rx_credits),
        .phy_tx_data(phy_tx_data),
        .phy_rx_data(phy_rx_data),
        .phy_tx_valid(phy_tx_valid),
        .phy_rx_valid(phy_rx_valid),
        .phy_tx_ready(phy_tx_ready),
        .phy_rx_ready(phy_rx_ready),
        .phy_tx_status(phy_tx_status),
        .phy_rx_status(phy_rx_status),
        .link_up(link_up),
        .link_width(link_width),
        .link_rate(link_rate),
        .link_training(link_training)
    );

    pcie_physical_layer #(
        .LANES(lanes_x8)
    ) u_physical_layer (
        .clk_phy(clk_phy),
        .rst_n_phy(rst_n_phy),
        .phy_tx_data(phy_tx_data),
        .phy_rx_data(phy_rx_data),
        .phy_tx_valid(phy_tx_valid),
        .phy_rx_valid(phy_rx_valid),
        .phy_tx_ready(phy_tx_ready),
        .phy_rx_ready(phy_rx_ready),
        .phy_tx_status(phy_tx_status),
        .phy_rx_status(phy_rx_status),
        .tx_data_p(tx_data_p),
        .tx_data_n(tx_data_n),
        .rx_data_p(rx_data_p),
        .rx_data_n(rx_data_n),
        .tx_clk_p(tx_clk_p),
        .tx_clk_n(tx_clk_n),
        .rx_clk_p(rx_clk_p),
        .rx_clk_n(rx_clk_n),
        .tx_elec_idle(tx_elec_idle),
        .phy_ready(phy_ready),
        .phy_status(phy_status)
    );

    // Configuration Space Management
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            cfg_command <= 16'h0007;
            cfg_status <= 16'h0010;
        end else begin
            cfg_command[0] <= axi_s_arvalid & axi_s_arready;
            cfg_command[1] <= axi_s_awvalid & axi_s_awready;
            cfg_status[18] <= link_up;
        end
    end

    // Power Management State Machine
    always_ff @(posedge clk_sys or negedge rst_n_sys) begin
        if (!rst_n_sys) begin
            power_state <= 2'b00;
        end else begin
            case (power_state)
                2'b00: if (cfg_command[8]) power_state <= 2'b01;
                2'b01: if (cfg_command[9]) power_state <= 2'b10;
                2'b10: if (!cfg_command[8]) power_state <= 2'b01;
                default: power_state <= 2'b00;
            endcase
        end
    end

endmodule
