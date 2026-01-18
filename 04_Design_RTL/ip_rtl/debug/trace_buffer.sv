//==============================================================================
// File: trace_buffer.sv
// Description: Trace Buffer for ETM/ITM/STM trace data
//              Implements circular buffer for non-invasive trace capture
// Version: 1.0
//==============================================================================

`timescale 1ns/1ps

module trace_buffer #(
    parameter int SIZE_KB = 8192,      // Size in KB
    parameter int DATA_WIDTH = 64,
    parameter int ATID_WIDTH = 8
) (
    // System interface
    input  logic                        clk_i,
    input  logic                        rst_ni,
    
    // Enable/control
    input  logic                        enable_i,
    
    // ATB input (from CoreSight matrix)
    input  logic [ATID_WIDTH-1:0]       atid_i,
    input  logic                        atvalid_i,
    input  logic [DATA_WIDTH-1:0]       atdata_i,
    input  logic                        atlast_i,
    output logic                        atready_o,
    
    // TPIU output (to external trace port)
    output logic                        tpiu_clk_o,
    output logic [31:0]                 tpiu_data_o,
    output logic                        tpiu_valid_o,
    output logic                        tpiu_sync_o,
    
    // Status
    output logic                        full_o,
    output logic [$clog2(SIZE_KB*1024/8)-1:0] level_o
);

    //============================================================================
    // Parameters
    //============================================================================
    localparam int BUFFER_SIZE = SIZE_KB * 1024 / 8;  // Entries, 8 bytes per entry
    localparam int PTR_WIDTH = $clog2(BUFFER_SIZE);
    localparam int WORD_SIZE = DATA_WIDTH / 8;  // 8 bytes
    
    localparam int TPIU_DATA_WIDTH = 32;
    localparam int TPIU_CLOCK_RATIO = 2;  // TPIU clock = 2x buffer clock (DDR)
    
    //============================================================================
    // Signal declarations
    //============================================================================
    // Buffer memory
    logic [DATA_WIDTH-1:0] buffer_mem [0:BUFFER_SIZE-1];
    logic [PTR_WIDTH-1:0]  wr_ptr, wr_ptr_next;
    logic [PTR_WIDTH-1:0]  rd_ptr, rd_ptr_next;
    logic                  buffer_full, buffer_empty;
    
    // Write interface
    logic                  wr_en;
    logic [DATA_WIDTH-1:0] wr_data;
    logic                  wr_last;
    logic [ATID_WIDTH-1:0] wr_atid;
    
    // Read interface
    logic                  rd_en;
    logic [DATA_WIDTH-1:0] rd_data;
    logic                  rd_last;
    logic [ATID_WIDTH-1:0] rd_atid;
    
    // TPIU serializer
    logic                  tpiu_clk;
    logic                  tpiu_clk_div;
    logic                  ser_data;
    logic [31:0]           ser_shift_reg;
    logic [4:0]            ser_bit_count;
    logic                  ser_valid;
    logic                  ser_busy;
    
    // Control
    logic                  auto_flush;
    logic                  flush_request;
    logic [$clog2(BUFFER_SIZE)-1:0] fill_level;
    
    //============================================================================
    // Buffer Memory (True Dual Port)
    //============================================================================
    // Write port
    always_ff @(posedge clk_i) begin
        if (wr_en) begin
            buffer_mem[wr_ptr] <= {atid_i, atdata_i, atlast_i};
        end
    end
    
    // Read port
    always_ff @(posedge clk_i) begin
        {rd_atid, rd_data, rd_last} <= buffer_mem[rd_ptr];
    end
    
    //============================================================================
    // Write Pointer Logic
    //============================================================================
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            wr_ptr <= '0;
        end else begin
            wr_ptr <= wr_ptr_next;
        end
    end
    
    assign wr_en = enable_i && atvalid_i && atready_o;
    
    always_comb begin
        wr_ptr_next = wr_ptr;
        
        if (wr_en) begin
            if (wr_ptr == BUFFER_SIZE-1) begin
                wr_ptr_next = '0;  // Wrap around
            end else begin
                wr_ptr_next = wr_ptr + 1;
            end
        end
    end
    
    //============================================================================
    // Read Pointer Logic
    //============================================================================
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            rd_ptr <= '0;
        end else begin
            rd_ptr <= rd_ptr_next;
        end
    end
    
    // Read when TPIU is ready
    assign rd_en = !buffer_empty && !ser_busy;
    
    always_comb begin
        rd_ptr_next = rd_ptr;
        
        if (rd_en) begin
            if (rd_ptr == BUFFER_SIZE-1) begin
                rd_ptr_next = '0;
            end else begin
                rd_ptr_next = rd_ptr + 1;
            end
        end
    end
    
    //============================================================================
    // Buffer Status
    //============================================================================
    assign buffer_empty = (wr_ptr == rd_ptr);
    assign buffer_full = (wr_ptr_next == rd_ptr) && wr_en;
    
    assign full_o = buffer_full;
    assign atready_o = enable_i && !buffer_full;
    
    // Fill level calculation
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            fill_level <= '0;
        end else begin
            if (wr_en && !rd_en) begin
                fill_level <= fill_level + 1;
            end else if (!wr_en && rd_en) begin
                fill_level <= fill_level - 1;
            end
        end
    end
    
    assign level_o = fill_level;
    
    //============================================================================
    // TPIU Output (Parallel to Serial)
    //============================================================================
    // TPIU clock generation (2x data rate for DDR)
    assign tpiu_clk_o = tpiu_clk;
    
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            tpiu_clk <= 1'b0;
            tpiu_clk_div <= 1'b0;
        end else begin
            tpiu_clk_div <= ~tpiu_clk_div;
            tpiu_clk <= tpiu_clk_div;
        end
    end
    
    // TPIU serializer
    always_ff @(posedge tpiu_clk) begin
        if (!rst_ni) begin
            ser_shift_reg <= '0;
            ser_bit_count <= '0;
            ser_valid <= 1'b0;
            ser_busy <= 1'b0;
        end else begin
            if (!ser_busy && rd_en) begin
                // Load new data
                ser_shift_reg <= rd_data;
                ser_bit_count <= 5'd31;  // 32 bits to send
                ser_valid <= 1'b1;
                ser_busy <= 1'b1;
            end else if (ser_valid) begin
                // Shift out data
                ser_shift_reg <= {ser_shift_reg[30:0], 1'b0};
                
                if (ser_bit_count == 0) begin
                    // Done
                    ser_valid <= 1'b0;
                    ser_busy <= rd_en;  // Continue if more data available
                    ser_bit_count <= 5'd31;
                end else begin
                    ser_bit_count <= ser_bit_count - 1;
                end
            end else begin
                ser_busy <= rd_en;
            end
        end
    end
    
    // TPIU output assignments
    assign tpiu_data_o = ser_shift_reg;
    assign tpiu_valid_o = ser_valid;
    assign tpiu_sync_o = rd_last;  // Sync indicates end of packet
    
    //============================================================================
    // Assertions
    //============================================================================
    initial begin
        if (SIZE_KB < 1) begin
            $error("Buffer size must be at least 1KB");
        end
        if (BUFFER_SIZE < 2) begin
            $error("Buffer too small");
        end
    end
    
    // Buffer overflow check
    assert property (@(posedge clk_i) disable iff (!rst_ni)
        !(wr_en && buffer_full))
        else $error("Trace buffer overflow");
    
    // Buffer underflow check
    assert property (@(posedge clk_i) disable iff (!rst_ni)
        !(rd_en && buffer_empty))
        else $error("Trace buffer underflow");
    
endmodule
