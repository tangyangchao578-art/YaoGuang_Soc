//==============================================================================
// File: swd_controller.sv
// Description: Serial Wire Debug (SWD) Controller
//              Implements ARM Debug Interface v5 SWD protocol
// Version: 1.0
//==============================================================================

`timescale 1ns/1ps

module swd_controller #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
) (
    // System interface
    input  logic                        clk_i,
    input  logic                        rst_ni,
    
    // SWD physical interface
    input  logic                        swd_clk_i,
    inout  logic                        swd_io_b,
    
    // Debug register interface
    output logic [ADDR_WIDTH-1:0]       addr_o,
    output logic [DATA_WIDTH-1:0]       wdata_o,
    output logic                        write_o,      // 1=write, 0=read
    output logic                        enable_o,     // 1=start transaction
    input  logic [DATA_WIDTH-1:0]       rdata_i,      // Read data
    input  logic                        ready_i,      // Transaction complete
    input  logic                        error_i       // Transaction error
);

    //============================================================================
    // Parameters
    //============================================================================
    localparam int SWD_HEADER_BITS = 8;
    localparam int SWD_ACK_BITS = 3;
    localparam int SWD_DATA_BITS = DATA_WIDTH;
    localparam int SWD_PARITY_BITS = 1;
    localparam int SWD_TURNAROUND = 1;
    
    // SWD Response codes
    localparam logic [2:0] ACK_OK    = 3'b001;
    localparam logic [2:0] ACK_WAIT  = 3'b010;
    localparam logic [2:0] ACK_FAULT = 3'b100;
    
    //============================================================================
    // Signal declarations
    //============================================================================
    // SWD state machine
    typedef enum logic [3:0] {
        STATE_IDLE,
        STATE_REQUEST,
        STATE_TURNAROUND,
        STATE_ACK,
        STATE_DATA,
        STATE_PARITY,
        STATE_TURNAROUND2,
        STATE_RESPONSE
    } swd_state_t;
    
    swd_state_t            state, state_next;
    
    // SWD line sampling
    logic                  swd_io_sampled;
    logic                  swd_io_drive;
    logic [DATA_WIDTH-1:0] swd_data_out;
    logic                  swd_parity_out;
    logic [SWD_HEADER_BITS-1:0] swd_request;
    
    // Transaction tracking
    logic                  transaction_active;
    logic                  is_write;
    logic [3:0]            apn_dp;        // AP(1) or DP(0)
    logic [2:0]            addr_bits;     // A[2:3]
    logic [SWD_ACK_BITS-1:0] ack_response;
    logic [DATA_WIDTH-1:0] read_data;
    logic                  read_parity;
    
    // Bit counters
    logic [5:0]            bit_count;
    logic [5:0]            bit_count_next;
    
    // Clock domain crossing (SWD clock to system clock)
    logic                  swd_clk_sync;
    logic                  swd_clk_prev;
    logic                  swd_clk_rising;
    logic                  swd_clk_falling;
    
    // Output registers
    logic [ADDR_WIDTH-1:0] addr_reg;
    logic [DATA_WIDTH-1:0] wdata_reg;
    logic                  write_reg;
    logic                  enable_reg;
    logic                  enable_next;
    
    //============================================================================
    // SWD Clock Synchronization
    //============================================================================
    always_ff @(posedge clk_i) begin
        swd_clk_sync <= swd_clk_i;
        swd_clk_prev <= swd_clk_sync;
    end
    
    assign swd_clk_rising = swd_clk_sync && !swd_clk_prev;
    assign swd_clk_falling = !swd_clk_sync && swd_clk_prev;
    
    //============================================================================
    // SWD I/O Bi-directional Buffer
    //============================================================================
    // Schmitt trigger input synchronizer
    always_ff @(posedge clk_i) begin
        swd_io_sampled <= swd_io_b;
    end
    
    // Output driver with enable
    assign swd_io_b = swd_io_drive ? swd_data_out[0] : 1'bZ;
    
    //============================================================================
    // Request Packet Construction
    //============================================================================
    // Request byte format: [Start:1, APnDP:1, RNW:1, A2:1, A3:1, Parity:1, Stop:1, Park:1]
    function [SWD_HEADER_BITS-1:0] build_request(
        input logic apndp,   // 1=AP, 0=DP
        input logic rnw,     // 1=read, 0=write
        input logic [1:0] addr
    );
        logic [5:0] header_bits;
        header_bits = {apndp, rnw, addr[1], addr[0]};
        build_request = {1'b1, header_bits, 1'b0, 1'b1, 1'b1};
        // Add parity to bits 5:0
        build_request[5] = ^header_bits;
    endfunction
    
    //============================================================================
    // SWD State Machine
    //============================================================================
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            state <= STATE_IDLE;
            bit_count <= '0;
            transaction_active <= 1'b0;
            is_write <= 1'b0;
            apn_dp <= '0;
            addr_bits <= '0;
            ack_response <= '0;
            read_data <= '0;
            read_parity <= '0;
        end else begin
            state <= state_next;
            bit_count <= bit_count_next;
            
            // State-specific logic
            unique case (state_next)
                STATE_REQUEST: begin
                    if (swd_clk_falling && !transaction_active) begin
                        // Start transmission on first falling edge
                        swd_request <= build_request(apn_dp, write_reg, addr_bits[1:0]);
                        swd_data_out <= {31'b0, build_request(apn_dp, write_reg, addr_bits[1:0])};
                    end
                end
                
                STATE_DATA: begin
                    if (swd_clk_falling) begin
                        if (is_write) begin
                            // Shift out write data
                            swd_data_out <= {1'b0, swd_data_out[31:1]};
                        end else begin
                            // Sample read data
                            read_data <= {swd_io_sampled, read_data[31:1]};
                        end
                    end
                end
                
                STATE_PARITY: begin
                    if (swd_clk_falling) begin
                        if (!is_write) begin
                            read_parity <= swd_io_sampled;
                        end
                    end
                end
                
                STATE_RESPONSE: begin
                    // Latch response
                    ack_response <= {swd_io_sampled, ack_response[2:1]};
                end
                
                default: begin
                    // No action
                end
            endcase
        end
    end
    
    // Next state logic
    always_comb begin
        state_next = state;
        bit_count_next = bit_count;
        enable_next = enable_reg;
        swd_io_drive = 1'b0;
        swd_data_out = '0;
        
        unique case (state)
            STATE_IDLE: begin
                bit_count_next = '0;
                if (enable_reg) begin
                    // Start new transaction
                    state_next = STATE_REQUEST;
                    transaction_active <= 1'b1;
                end
            end
            
            STATE_REQUEST: begin
                swd_io_drive = 1'b1;
                // First bit (Start) driven on first falling edge
                swd_data_out = {31'b0, swd_request[7]};
                
                if (swd_clk_falling) begin
                    if (bit_count == 7) begin
                        // Request complete
                        state_next = STATE_TURNAROUND;
                        bit_count_next = '0;
                    end else begin
                        bit_count_next = bit_count + 1;
                        swd_data_out = {31'b0, swd_request[7-bit_count]};
                    end
                end
            end
            
            STATE_TURNAROUND: begin
                // Host tristates, target drives after turnaround
                swd_io_drive = 1'b0;
                
                if (swd_clk_falling) begin
                    if (bit_count == SWD_TURNAROUND-1) begin
                        state_next = STATE_ACK;
                        bit_count_next = '0;
                    end else begin
                        bit_count_next = bit_count + 1;
                    end
                end
            end
            
            STATE_ACK: begin
                // Sample ACK on rising edges
                if (swd_clk_rising) begin
                    if (bit_count == 2) begin
                        // ACK complete, check for WAIT/FAULT
                        if (ack_response == ACK_OK) begin
                            if (is_write) begin
                                state_next = STATE_DATA;
                            end else begin
                                state_next = STATE_TURNAROUND2;
                            end
                            bit_count_next = '0;
                        end else if (ack_response == ACK_WAIT) begin
                            // Retry
                            state_next = STATE_REQUEST;
                            bit_count_next = '0;
                            transaction_active <= 1'b0;
                            enable_next = 1'b1;  // Retry
                        end else begin
                            // FAULT - abort
                            state_next = STATE_IDLE;
                            transaction_active <= 1'b0;
                            enable_next = 1'b0;
                        end
                    end else begin
                        bit_count_next = bit_count + 1;
                    end
                end
            end
            
            STATE_DATA: begin
                swd_io_drive = is_write;
                
                if (swd_clk_falling) begin
                    if (bit_count == 31) begin
                        state_next = STATE_PARITY;
                        bit_count_next = '0;
                    end else begin
                        bit_count_next = bit_count + 1;
                    end
                end
            end
            
            STATE_PARITY: begin
                swd_io_drive = is_write;  // Write parity
                
                if (swd_clk_falling) begin
                    if (is_write) begin
                        swd_data_out = {31'b0, swd_parity_out};
                    end
                    state_next = STATE_TURNAROUND2;
                    bit_count_next = '0;
                end
            end
            
            STATE_TURNAROUND2: begin
                swd_io_drive = 1'b0;
                
                if (swd_clk_falling) begin
                    if (bit_count == SWD_TURNAROUND-1) begin
                        if (is_write) begin
                            // Write complete, expect ACK on next turnaround
                            state_next = STATE_ACK;
                        end else begin
                            // Read data phase
                            state_next = STATE_DATA;
                        end
                        bit_count_next = '0;
                    end else begin
                        bit_count_next = bit_count + 1;
                    end
                end
            end
            
            STATE_RESPONSE: begin
                // Final phase for read transactions
                if (swd_clk_falling) begin
                    if (bit_count == 2) begin
                        // Check parity
                        if (read_parity == ^read_data) begin
                            state_next = STATE_IDLE;
                            transaction_active <= 1'b0;
                            enable_next = 1'b0;
                        end else begin
                            // Parity error - retry
                            state_next = STATE_REQUEST;
                            transaction_active <= 1'b0;
                            enable_next = 1'b1;
                        end
                        bit_count_next = '0;
                    end else begin
                        bit_count_next = bit_count + 1;
                    end
                end
            end
            
            default: state_next = STATE_IDLE;
        endcase
    end
    
    //============================================================================
    // Output Assignments
    //============================================================================
    assign addr_o = addr_reg;
    assign wdata_o = wdata_reg;
    assign write_o = write_reg;
    assign enable_o = enable_reg;
    
    // Latch outputs on enable
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            addr_reg <= '0;
            wdata_reg <= '0;
            write_reg <= '0;
            enable_reg <= 1'b0;
        end else begin
            if (enable_i && ready_i) begin
                // Transaction complete, latch new request
                addr_reg <= addr_o;
                wdata_reg <= wdata_o;
                write_reg <= write_o;
                enable_reg <= 1'b0;
            end else if (enable_i) begin
                // Keep request stable during transaction
                enable_reg <= 1'b1;
            end
        end
    end
    
    // Parity calculation for write data
    assign swd_parity_out = ^wdata_reg;
    
    //============================================================================
    // Transaction Complete Detection
    //============================================================================
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            // Nothing
        end else begin
            if (ready_i && enable_reg) begin
                enable_reg <= 1'b0;
            end
        end
    end
    
    //============================================================================
    // Assertions
    //============================================================================
    // Address width check
    initial begin
        if (ADDR_WIDTH < 32) begin
            $warning("ADDR_WIDTH less than 32, high bits will be zero");
        end
    end
    
    // ACK response monitoring
    assert property (@(posedge clk_i) transaction_active |-> !$stable(ack_response))
        else $warning("ACK response should change during transaction");
    
endmodule
