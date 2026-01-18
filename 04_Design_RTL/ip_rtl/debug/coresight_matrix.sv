//==============================================================================
// File: coresight_matrix.sv
// Description: CoreSight Crossbar Matrix for ATB trace routing
//              Connects multiple trace sources to multiple sinks
// Version: 1.0
//==============================================================================

`timescale 1ns/1ps

module coresight_matrix #(
    parameter int NUM_MASTERS = 6,
    parameter int NUM_SLAVES = 2,
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 64,
    parameter int ATID_WIDTH = 8
) (
    // System interface
    input  logic                        clk_i,
    input  logic                        rst_ni,
    
    // Master interfaces (trace sources)
    input  logic [NUM_MASTERS-1:0][ATID_WIDTH-1:0]  m_atid_i,
    input  logic [NUM_MASTERS-1:0]                    m_atvalid_i,
    input  logic [NUM_MASTERS-1:0][DATA_WIDTH-1:0]   m_atdata_i,
    input  logic [NUM_MASTERS-1:0]                    m_atlast_i,
    output logic [NUM_MASTERS-1:0]                    m_atready_o,
    
    // Slave interfaces (trace sinks)
    output logic [NUM_SLAVES-1:0][ATID_WIDTH-1:0]     s_atid_o,
    output logic [NUM_SLAVES-1:0]                     s_atvalid_o,
    output logic [NUM_SLAVES-1:0][DATA_WIDTH-1:0]     s_atdata_o,
    output logic [NUM_SLAVES-1:0]                     s_atlast_o,
    input  logic [NUM_SLAVES-1:0]                     s_atready_i
);

    //============================================================================
    // Parameters
    //============================================================================
    localparam int FIFO_DEPTH = 8;
    localparam int NUM_MASTERS_W = NUM_MASTERS > 1 ? $clog2(NUM_MASTERS) : 1;
    localparam int NUM_SLAVES_W = NUM_SLAVES > 1 ? $clog2(NUM_SLAVES) : 1;
    
    //============================================================================
    // Type definitions
    //============================================================================
    typedef struct packed {
        logic [ATID_WIDTH-1:0] atid;
        logic [DATA_WIDTH-1:0] atdata;
        logic                  atlast;
        logic [NUM_MASTERS_W-1:0] source;
    } trace_packet_t;
    
    typedef struct packed {
        logic [ATID_WIDTH-1:0] atid;
        logic [DATA_WIDTH-1:0] atdata;
        logic                  atlast;
    } sink_packet_t;
    
    //============================================================================
    // Signal declarations
    //============================================================================
    // Input FIFO signals
    trace_packet_t [NUM_MASTERS-1:0] fifo_in;
    logic [NUM_MASTERS-1:0]         fifo_push;
    logic [NUM_MASTERS-1:0]         fifo_full;
    logic [NUM_MASTERS-1:0]         fifo_empty;
    trace_packet_t [NUM_MASTERS-1:0] fifo_out;
    logic [NUM_MASTERS-1:0]         fifo_pop;
    
    // Arbitration signals
    logic [NUM_MASTERS-1:0]         grant;
    logic [NUM_MASTERS-1:0]         request;
    logic [NUM_MASTERS-1:0]         active_request;
    logic [NUM_MASTERS_W-1:0]       arb_winner;
    logic [NUM_MASTERS_W-1:0]       arb_winner_next;
    logic [NUM_MASTERS-1:0]         round_robin_mask;
    
    // Output FIFO signals
    sink_packet_t [NUM_SLAVES-1:0]  out_fifo_in;
    logic [NUM_SLAVES-1:0]          out_fifo_push;
    logic [NUM_SLAVES-1:0]          out_fifo_full;
    logic [NUM_SLAVES-1:0]          out_fifo_empty;
    sink_packet_t [NUM_SLAVES-1:0]  out_fifo_out;
    logic [NUM_SLAVES-1:0]          out_fifo_pop;
    
    // Static routing configuration
    logic [NUM_MASTERS-1:0][NUM_SLAVES_W-1:0] route_config;
    
    //============================================================================
    // Static Route Configuration
    //============================================================================
    // Default routing: Master 0-3 (ETMs) -> TPIU (slave 0)
    //                  Master 4 (ITM) -> Trace buffer (slave 1)
    //                  Master 5 (STM) -> Trace buffer (slave 1)
    always_comb begin
        route_config = '0;
        for (int i = 0; i < NUM_MASTERS; i++) begin
            if (i < 4) begin
                route_config[i] = '0;  // Route to TPIU
            end else begin
                route_config[i] = NUM_SLAVES > 1 ? 1 : 0;  // Route to trace buffer
            end
        end
    end
    
    //============================================================================
    // Input FIFOs (per master)
    //============================================================================
    generate
        for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_input_fifo
            // Prepare FIFO input
            assign fifo_in[m] = '{
                atid:    m_atid_i[m],
                atdata:  m_atdata_i[m],
                atlast:  m_atlast_i[m],
                source:  NUM_MASTERS_W'(m)
            };
            
            // FIFO control
            assign fifo_push[m] = m_atvalid_i[m] && !fifo_full[m];
            assign m_atready_o[m] = !fifo_full[m];
            
            sync_fifo #(
                .WIDTH($bits(trace_packet_t)),
                .DEPTH(FIFO_DEPTH)
            ) u_fifo (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .wr_en_i(fifo_push[m]),
                .wr_data_i(fifo_in[m]),
                .full_o(fifo_full[m]),
                .rd_en_i(fifo_pop[m]),
                .rd_data_o(fifo_out[m]),
                .empty_o(fifo_empty[m])
            );
        end
    endgenerate
    
    //============================================================================
    // Arbitration Logic
    //============================================================================
    // Round-robin arbitration with priority
    always_comb begin
        // Default: no grant
        grant = '0;
        arb_winner_next = arb_winner;
        round_robin_mask = '0;
        
        // Mask off masters below current priority
        for (int i = 0; i < NUM_MASTERS; i++) begin
            if (i <= arb_winner) begin
                round_robin_mask[i] = 1'b1;
            end
        end
        
        // Combine request with round-robin mask
        active_request = request & ~round_robin_mask;
        
        // First check masked requests
        if (active_request != '0) begin
            // Find highest priority masked request
            for (int i = NUM_MASTERS-1; i >= 0; i--) begin
                if (active_request[i]) begin
                    grant[i] = 1'b1;
                    arb_winner_next = NUM_MASTERS_W'(i);
                    break;
                end
            end
        end else begin
            // Check unmasked requests (wrap around)
            active_request = request & round_robin_mask;
            if (active_request != '0) begin
                for (int i = NUM_MASTERS-1; i >= 0; i--) begin
                    if (active_request[i]) begin
                        grant[i] = 1'b1;
                        arb_winner_next = NUM_MASTERS_W'(i);
                        break;
                    end
                end
            end else begin
                // No requests, advance priority
                if (arb_winner < NUM_MASTERS_W'(NUM_MASTERS-1)) begin
                    arb_winner_next = arb_winner + 1;
                end else begin
                    arb_winner_next = '0;
                end
            end
        end
    end
    
    // Current winner register
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            arb_winner <= '0;
        end else begin
            arb_winner <= arb_winner_next;
        end
    end
    
    // Generate request signals from non-empty FIFOs
    always_comb begin
        for (int i = 0; i < NUM_MASTERS; i++) begin
            request[i] = !fifo_empty[i];
        end
    end
    
    //============================================================================
    // Crossbar Switch Fabric
    //============================================================================
    // Route winner to appropriate slave
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            // Outputs deasserted
            for (int s = 0; s < NUM_SLAVES; s++) begin
                out_fifo_push[s] <= 1'b0;
                out_fifo_in[s] <= '0;
            end
        end else begin
            // Default: no push
            out_fifo_push = '0;
            
            // If there's a grant and output FIFO has space
            if (grant != '0) begin
                // Find which master won
                for (int m = 0; m < NUM_MASTERS; m++) begin
                    if (grant[m]) begin
                        // Determine target slave based on route config
                        logic [NUM_SLAVES_W-1:0] target_slave;
                        target_slave = route_config[m];
                        
                        // Check if target FIFO has space
                        if (!out_fifo_full[target_slave]) begin
                            // Push to target FIFO
                            out_fifo_in[target_slave] = '{
                                atid:   fifo_out[m].atid,
                                atdata: fifo_out[m].atdata,
                                atlast: fifo_out[m].atlast
                            };
                            out_fifo_push[target_slave] = 1'b1;
                            fifo_pop[m] = 1'b1;
                        end else begin
                            // Backpressure - pop later
                            fifo_pop[m] = 1'b0;
                        end
                        break;
                    end
                end
            end else begin
                // No grant, pop nothing
                fifo_pop = '0;
            end
        end
    end
    
    //============================================================================
    // Output FIFOs (per slave)
    //============================================================================
    generate
        for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_output_fifo
            sync_fifo #(
                .WIDTH($bits(sink_packet_t)),
                .DEPTH(FIFO_DEPTH * 2)  // Larger output buffer
            ) u_fifo (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .wr_en_i(out_fifo_push[s]),
                .wr_data_i(out_fifo_in[s]),
                .full_o(out_fifo_full[s]),
                .rd_en_i(out_fifo_pop[s]),
                .rd_data_o(out_fifo_out[s]),
                .empty_o(out_fifo_empty[s])
            );
            
            // Output assignments
            assign s_atid_o[s]    = out_fifo_out[s].atid;
            assign s_atdata_o[s]  = out_fifo_out[s].atdata;
            assign s_atlast_o[s]  = out_fifo_out[s].atlast;
            
            // Pop when slave is ready
            assign out_fifo_pop[s] = s_atvalid_o[s] && s_atready_i[s];
            
            // Output valid
            assign s_atvalid_o[s] = !out_fifo_empty[s];
        end
    endgenerate
    
    //============================================================================
    // Assertions
    //============================================================================
    initial begin
        if (NUM_MASTERS < 1) begin
            $error("NUM_MASTERS must be at least 1");
        end
        if (NUM_SLAVES < 1) begin
            $error("NUM_SLAVES must be at least 1");
        end
    end
    
    // ATID uniqueness (should be unique per source)
    assert property (@(posedge clk_i) disable iff (!rst_ni)
        $onehot0(|{m_atvalid_i}))
        else $warning("Multiple ATID sources active simultaneously");
    
endmodule

//==============================================================================
// Internal module: Synchronous FIFO
//==============================================================================
module sync_fifo #(
    parameter int WIDTH = 64,
    parameter int DEPTH = 8
) (
    input  logic              clk_i,
    input  logic              rst_ni,
    input  logic              wr_en_i,
    input  logic [WIDTH-1:0]  wr_data_i,
    output logic              full_o,
    input  logic              rd_en_i,
    output logic [WIDTH-1:0]  rd_data_o,
    output logic              empty_o
);
    
    localparam int PTR_WIDTH = $clog2(DEPTH);
    
    logic [WIDTH-1:0]         mem [DEPTH-1:0];
    logic [PTR_WIDTH:0]       wr_ptr, rd_ptr;
    logic                     full_next, empty_next;
    
    // Memory write
    always_ff @(posedge clk_i) begin
        if (wr_en_i) begin
            mem[wr_ptr[PTR_WIDTH-1:0]] <= wr_data_i;
        end
    end
    
    // Read data
    assign rd_data_o = mem[rd_ptr[PTR_WIDTH-1:0]];
    
    // Write pointer
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            wr_ptr <= '0;
        end else if (wr_en_i) begin
            wr_ptr <= wr_ptr + 1;
        end
    end
    
    // Read pointer
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            rd_ptr <= '0;
        end else if (rd_en_i) begin
            rd_ptr <= rd_ptr + 1;
        end
    end
    
    // Status
    assign full_o  = (wr_ptr[PTR_WIDTH] != rd_ptr[PTR_WIDTH]) && 
                     (wr_ptr[PTR_WIDTH-1:0] == rd_ptr[PTR_WIDTH-1:0]);
    assign empty_o = (wr_ptr == rd_ptr);
    
endmodule
