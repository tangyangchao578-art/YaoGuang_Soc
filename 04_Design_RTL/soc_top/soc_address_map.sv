// ============================================================================
// Module: soc_address_map
// Description: YaoGuang SoC 地址映射定义
// Author: YaoGuang RTL Team
// Version: V1.0
// Date: 2026-01-18
// ============================================================================

`include "soc_package.sv"

module soc_address_map (
    // AXI4 Master 接口 (来自 NoC)
    input  logic                        axi_clk,
    input  logic                        axi_rst_n,
    
    // 地址输入
    input  logic [31:0]                 s_awaddr,
    input  logic [31:0]                 s_araddr,
    
    // 从设备选择输出
    output logic                        m_boot_rom_sel,
    output logic                        m_safety_island_sel,
    output logic                        m_npu_cluster_sel [4],
    output logic                        m_l3_cache_sel,
    output logic                        m_gpu_sel,
    output logic                        m_isp_sel,
    output logic                        m_display_sel,
    output logic                        m_crypto_sel,
    output logic                        m_pcie_x8_sel,
    output logic                        m_pcie_x4_sel,
    output logic                        m_usb_sel,
    output logic                        m_ethernet_sel,
    output logic                        m_apb_periph_sel,
    output logic                        m_ddr_ctrl_sel,
    
    // 错误响应
    output logic                        m_dec_error
);
    
    // ============================================================================
    // 地址解码逻辑
    // ============================================================================
    
    // 地址高位解码
    logic [7:0] addr_upper;
    assign addr_upper = s_awaddr[31:24];
    
    // Boot ROM 选择 (0x0000_0000 - 0x0FFF_FFFF)
    assign m_boot_rom_sel = (addr_upper == 8'h00);
    
    // Safety Island 选择 (0x1000_0000 - 0x1FFF_FFFF)
    assign m_safety_island_sel = (addr_upper == 8'h10);
    
    // NPU Cluster 选择 (0x2000_0000 - 0x5FFF_FFFF)
    assign m_npu_cluster_sel[0] = (addr_upper == 8'h20);
    assign m_npu_cluster_sel[1] = (addr_upper == 8'h30);
    assign m_npu_cluster_sel[2] = (addr_upper == 8'h40);
    assign m_npu_cluster_sel[3] = (addr_upper == 8'h50);
    
    // L3 Cache 选择 (0x6000_0000 - 0x6FFF_FFFF)
    assign m_l3_cache_sel = (addr_upper == 8'h60);
    
    // GPU 选择 (0x7000_0000 - 0x7FFF_FFFF)
    assign m_gpu_sel = (addr_upper == 8'h70);
    
    // ISP 选择 (0x8000_0000 - 0x8FFF_FFFF)
    assign m_isp_sel = (addr_upper == 8'h80);
    
    // Display 选择 (0x9000_0000 - 0x9FFF_FFFF)
    assign m_display_sel = (addr_upper == 8'h90);
    
    // Crypto 选择 (0xA000_0000 - 0xAFFF_FFFF)
    assign m_crypto_sel = (addr_upper == 8'hA0);
    
    // PCIe x8 选择 (0xB000_0000 - 0xBFFF_FFFF)
    assign m_pcie_x8_sel = (addr_upper == 8'hB0);
    
    // PCIe x4 选择 (0xC000_0000 - 0xCFFF_FFFF)
    assign m_pcie_x4_sel = (addr_upper == 8'hC0);
    
    // USB 选择 (0xD000_0000 - 0xDFFF_FFFF)
    assign m_usb_sel = (addr_upper == 8'hD0);
    
    // Ethernet 选择 (0xE000_0000 - 0xEFFF_FFFF)
    assign m_ethernet_sel = (addr_upper == 8'hE0);
    
    // APB 外设选择 (0xF000_0000 - 0xFEFF_FFFF)
    assign m_apb_periph_sel = (addr_upper[7:4] == 4'hF);
    
    // DDR 控制器选择 (0xFF00_0000 - 0xFFFF_FFFF)
    assign m_ddr_ctrl_sel = (addr_upper == 8'hFF);
    
    // 地址解码错误检测
    always_comb begin
        m_dec_error = 1'b0;
        
        if (!m_boot_rom_sel && !m_safety_island_sel &&
            !m_npu_cluster_sel[0] && !m_npu_cluster_sel[1] &&
            !m_npu_cluster_sel[2] && !m_npu_cluster_sel[3] &&
            !m_l3_cache_sel && !m_gpu_sel && !m_isp_sel &&
            !m_display_sel && !m_crypto_sel && !m_pcie_x8_sel &&
            !m_pcie_x4_sel && !m_usb_sel && !m_ethernet_sel &&
            !m_apb_periph_sel && !m_ddr_ctrl_sel) begin
            m_dec_error = 1'b1;
        end
    end
    
endmodule
