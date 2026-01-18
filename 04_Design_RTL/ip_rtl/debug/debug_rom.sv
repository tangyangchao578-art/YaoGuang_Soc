//==============================================================================
// File: debug_rom.sv
// Description: Debug ROM for DAP ROM Table
//              Contains CoreSight component identification and address mapping
// Version: 1.0
//==============================================================================

`timescale 1ns/1ps

module debug_rom #(
    parameter int SIZE = 1024,       // Size in bytes
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
) (
    // System interface
    input  logic                        clk_i,
    input  logic                        rst_ni,
    
    // Read interface
    input  logic [ADDR_WIDTH-1:0]       addr_i,
    output logic [DATA_WIDTH-1:0]       rdata_o,
    output logic                        ready_o
);

    //============================================================================
    // Parameters
    //============================================================================
    localparam int NUM_ENTRIES = SIZE / 4;
    localparam int PTR_WIDTH = $clog2(NUM_ENTRIES);
    localparam int ROM_WIDTH = DATA_WIDTH;
    
    // CoreSight ROM Entry Format:
    // [31:12] = Component address (bits [31:12])
    // [11:0]  = Format/type (0x0 = end, 0x1 = 4KB, 0x2 = 16KB, 0x3 = 64KB, 0xC = power, etc.)
    
    // Component IDs
    localparam logic [31:0] PID0 = 32'h00000004;  // Part number [7:0]
    localparam logic [31:0] PID1 = 32'h00000000;  // Part number [15:8]
    localparam logic [31:0] PID2 = 32'h00000000;  // Variant[3:0] + JEP106 ID[6:0]
    localparam logic [31:0] PID3 = 32'h00000000;  // JEP106 cont.
    localparam logic [31:0] PID4 = 32'h00000000;  // Rev + CMOD + size
    localparam logic [31:0] PID5 = 32'h00000000;
    localparam logic [31:0] PID6 = 32'h00000000;
    localparam logic [31:0] PID7 = 32'h00000000;
    
    localparam logic [31:0] CID0 = 32'h0000000D;  // PrimeCell class
    localparam logic [31:0] CID1 = 32'h00000010;
    localparam logic [31:0] CID2 = 32'h00000000;
    localparam logic [31:0] CID3 = 32'h00000005;
    
    // ROM Table entries (8-byte aligned)
    localparam logic [31:0] ROM_CPU0_ETM = 32'h10010001;  // @0x10010000, 4KB component
    localparam logic [31:0] ROM_CPU1_ETM = 32'h10020001;
    localparam logic [31:0] ROM_CPU2_ETM = 32'h10030001;
    localparam logic [31:0] ROM_CPU3_ETM = 32'h10040001;
    localparam logic [31:0] ROM_ITM    = 32'h10050001;
    localparam logic [31:0] ROM_TPIU   = 32'h10060001;
    localparam logic [31:0] ROM_DAP    = 32'hF8000001;
    localparam logic [31:0] ROM_END    = 32'h00000000;   // End marker
    
    //============================================================================
    // Signal declarations
    //============================================================================
    logic [PTR_WIDTH-1:0]   rom_addr;
    logic [ROM_WIDTH-1:0]   rom_data;
    logic [ROM_WIDTH-1:0]   rom_data_reg;
    logic                   valid_access;
    
    //============================================================================
    // ROM Address Mapping
    //============================================================================
    // ROM structure (0xFC0 - 0xFFF: PID/CID, 0x000-0x7FC: Component pointers)
    // ROM Table at 0xFC0, component entries follow
    
    // Extract word address from byte address
    assign rom_addr = addr_i[PTR_WIDTH+1:2];
    
    // Generate ROM data based on address
    always_comb begin
        rom_data = '0;
        valid_access = 1'b1;
        
        case (rom_addr)
            // ROM Header
            10'h3F0: rom_data = {24'h0, 8'h30};  // ROM size = 256 entries (1KB)
            10'h3F1: rom_data = ROM_END;         // Reserved
            10'h3F2: rom_data = ROM_END;         // Reserved
            10'h3F3: rom_data = ROM_END;         // Reserved
            
            // PID/CID (0xFC0-0xFFF)
            10'h3F8: rom_data = PID0;
            10'h3F9: rom_data = PID1;
            10'h3FA: rom_data = PID2;
            10'h3FB: rom_data = PID3;
            10'h3FC: rom_data = PID4;
            10'h3FD: rom_data = PID5;
            10'h3FE: rom_data = PID6;
            10'h3FF: rom_data = PID7;
            10'h400: rom_data = CID0;
            10'h401: rom_data = CID1;
            10'h402: rom_data = CID2;
            10'h403: rom_data = CID3;
            
            // Component entries (0x000-0x01C)
            10'h000: rom_data = ROM_CPU0_ETM;
            10'h001: rom_data = ROM_CPU1_ETM;
            10'h002: rom_data = ROM_CPU2_ETM;
            10'h003: rom_data = ROM_CPU3_ETM;
            10'h004: rom_data = ROM_ITM;
            10'h005: rom_data = ROM_TPIU;
            10'h006: rom_data = ROM_DAP;
            10'h007: rom_data = ROM_END;  // End of table
            
            // Reserved entries
            default: begin
                if (rom_addr >= 10'h008 && rom_addr <= 10'h3EF) begin
                    rom_data = ROM_END;  // Reserved/unused entries
                end else begin
                    valid_access = 1'b0;
                end
            end
        endcase
    end
    
    //============================================================================
    // Output Register
    //============================================================================
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            rom_data_reg <= '0;
            ready_o <= 1'b0;
        end else begin
            rom_data_reg <= rom_data;
            ready_o <= valid_access;
        end
    end
    
    assign rdata_o = rom_data_reg;
    
    //============================================================================
    // ROM Implementation (Distributed RAM)
    //============================================================================
    // Use distributed RAM for ROM content
    (* rom_style = "distributed" *)
    logic [ROM_WIDTH-1:0] rom_array [0:NUM_ENTRIES-1];
    
    // Initialize ROM from case statement
    initial begin
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            rom_array[i] = '0;
        end
        // PID/CID
        rom_array[10'h3F0] = {24'h0, 8'h30};
        rom_array[10'h3F8] = PID0;
        rom_array[10'h3F9] = PID1;
        rom_array[10'h3FA] = PID2;
        rom_array[10'h3FB] = PID3;
        rom_array[10'h3FC] = PID4;
        rom_array[10'h3FD] = PID5;
        rom_array[10'h3FE] = PID6;
        rom_array[10'h3FF] = PID7;
        rom_array[10'h400] = CID0;
        rom_array[10'h401] = CID1;
        rom_array[10'h402] = CID2;
        rom_array[10'h403] = CID3;
        // Component entries
        rom_array[10'h000] = ROM_CPU0_ETM;
        rom_array[10'h001] = ROM_CPU1_ETM;
        rom_array[10'h002] = ROM_CPU2_ETM;
        rom_array[10'h003] = ROM_CPU3_ETM;
        rom_array[10'h004] = ROM_ITM;
        rom_array[10'h005] = ROM_TPIU;
        rom_array[10'h006] = ROM_DAP;
        rom_array[10'h007] = ROM_END;
    end
    
    // ROM read
    always_ff @(posedge clk_i) begin
        if (valid_access) begin
            rom_data_reg <= rom_array[rom_addr];
        end
    end
    
    //============================================================================
    // Assertions
    //============================================================================
    initial begin
        if (SIZE % 4 != 0) begin
            $error("ROM size must be multiple of 4 bytes");
        end
        if (SIZE < 256) begin
            $warning("ROM size less than 256 bytes may not contain all required entries");
        end
    end
    
    // Valid access check
    assert property (@(posedge clk_i) disable iff (!rst_ni)
        ready_o |-> valid_access)
        else $error("Invalid ROM access");
    
endmodule
