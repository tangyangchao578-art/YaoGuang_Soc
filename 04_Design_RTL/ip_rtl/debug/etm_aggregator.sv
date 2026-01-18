//==============================================================================
// File: etm_aggregator.sv
// Description: ETM (Embedded Trace Macrocell) Aggregator
//              Combines trace data from multiple ETMs into single stream
// Version: 1.0
//==============================================================================

`timescale 1ns/1ps

module etm_aggregator #(
    parameter int NUM_ETMS = 4,
    parameter int DATA_WIDTH = 64,
    parameter int ATID_WIDTH = 8
) (
    // System interface
    input  logic                        clk_i,
    input  logic                        rst_ni,
    
    // Global enable
    input  logic                        enable_i,
    
    // ETM control outputs
    output logic [NUM_ETMS-1:0]         etm_enable_o,
    
    // ETM inputs (from each CPU core)
    input  logic [NUM_ETMS-1:1][ATID_WIDTH-1:0]  etm_atid_i,
    input  logic [NUM_ETMS-1:1]                   etm_atvalid_i,
    input  logic [NUM_ETMS-1:1][DATA_WIDTH-1:0]   etm_atdata_i,
    input  logic [NUM_ETMS-1:1]                   etm_atlast_i,
    output logic [NUM_ETMS-1:1]                   etm_atready_o,
    
    // Aggregated output (to TPIU)
    output logic [ATID_WIDTH-1:0]        agg_atid_o,
    output logic                         agg_atvalid_o,
    output logic [DATA_WIDTH-1:0]        agg_atdata_o,
    output logic                         agg_atlast_o,
    input  logic                         agg_atready_i
);

    //============================================================================
    // Parameters
    //============================================================================
    localparam int NUM_ETMS_W = NUM_ETMS > 1 ? $clog2(NUM_ETMS) : 1;
    localparam int FIFO_DEPTH = 16;
    
    //============================================================================
    // Signal declarations
    //============================================================================
    // Input FIFO signals
    logic [NUM_ETMS-1:0]         fifo_push;
    logic [NUM_ETMS-1:0]         fifo_full;
    logic [NUM_ETMS-1:0]         fifo_empty;
    logic [NUM_ETMS-1:0][DATA_WIDTH-1:0] fifo_din;
    logic [NUM_ETMS-1:0][DATA_WIDTH-1:0] fifo_dout;
    logic [NUM_ETMS-1:0]         fifo_pop;
    
    // Arbitration
    logic [NUM_ETMS-1:0]         request;
    logic [NUM_ETMS-1:0]         grant;
    logic [NUM_ETMS_W-1:0]       arb_winner;
    logic                        packet_in_progress;
    logic [NUM_ETMS_W-1:0]       current_source;
    
    // Output
    logic [DATA_WIDTH-1:0]       output_data;
    logic                        output_valid;
    logic                        output_last;
    logic                        output_ready;
    
    // ATID encoding: MSB = source, LSB = packet type
    logic [ATID_WIDTH-1:0]       output_atid;
    
    //============================================================================
    // ETM Enable Control
    //============================================================================
    assign etm_enable_o = {NUM_ETMS-1{enable_i}};
    
    //============================================================================
    // Input FIFOs per ETM
    //============================================================================
    generate
        for (genvar e = 0; e < NUM_ETMS; e++) begin : gen_etm_fifo
            // Prepare FIFO input (inject ATID with source encoding)
            assign fifo_din[e] = etm_atdata_i[e];
            
            // FIFO control
            assign fifo_push[e] = etm_atvalid_i[e] && !fifo_full[e];
            assign etm_atready_o[e] = !fifo_full[e];
            
            sync_fifo #(
                .WIDTH(DATA_WIDTH),
                .DEPTH(FIFO_DEPTH)
            ) u_fifo (
                .clk_i(clk_i),
                .rst_ni(rst_ni),
                .wr_en_i(fifo_push[e]),
                .wr_data_i(fifo_din[e]),
                .full_o(fifo_full[e]),
                .rd_en_i(fifo_pop[e]),
                .rd_data_o(fifo_dout[e]),
                .empty_o(fifo_empty[e])
            );
        end
    endgenerate
    
    //============================================================================
    // Round-Robin Arbitration
    //============================================================================
    // Priority-based round-robin: higher index has priority initially
    always_comb begin
        grant = '0;
        
        // Scan from highest priority to lowest
        for (int i = NUM_ETMS-1; i >= 0; i--) begin
            if (request[i]) begin
                grant[i] = 1'b1;
                break;
            end
        end
        
        // If no request, check wrap-around (lower priority gets chance)
        if (grant == '0) begin
            for (int i = 0; i < NUM_ETMS; i++) begin
                if (request[i]) begin
                    grant[i] = 1'b1;
                    break;
                end
            end
        end
    end
    
    // Request generation
    always_comb begin
        for (int i = 0; i < NUM_ETMS; i++) begin
            request[i] = !fifo_empty[i];
        end
    end
    
    //============================================================================
    // Output Selection
    //============================================================================
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            current_source <= '0;
            packet_in_progress <= 1'b0;
            output_valid <= 1'b0;
        end else begin
            if (enable_i) begin
                if (output_valid && output_ready) begin
                    // Output consumed, check for more from same source
                    if (output_last) begin
                        packet_in_progress <= 1'b0;
                    end
                end
                
                if (!packet_in_progress && grant != '0) begin
                    // Start new packet from winner
                    for (int i = 0; i < NUM_ETMS; i++) begin
                        if (grant[i]) begin
                            current_source <= NUM_ETMS_W'(i);
                            packet_in_progress <= 1'b1;
                            break;
                        end
                    end
                end
            end else begin
                output_valid <= 1'b0;
                packet_in_progress <= 1'b0;
            end
        end
    end
    
    // Data path
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            output_data <= '0;
            output_last <= 1'b0;
            output_valid <= 1'b0;
        end else begin
            if (enable_i) begin
                if (output_valid && output_ready) begin
                    // Output consumed
                    output_valid <= 1'b0;
                end
                
                if (!output_valid && grant != '0 && !packet_in_progress) begin
                    // Select data from winner
                    for (int i = 0; i < NUM_ETMS; i++) begin
                        if (grant[i]) begin
                            output_data <= fifo_dout[i];
                            output_last <= fifo_dout[i][DATA_WIDTH-1];  // Assume ATLAST in MSB
                            output_valid <= 1'b1;
                            fifo_pop[i] <= 1'b1;
                            break;
                        end
                    end
                end else begin
                    fifo_pop = '0;
                end
            end
        end
    end
    
    // Continue packet from same source
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            fifo_pop = '0;
        end else begin
            fifo_pop = '0;
            
            if (enable_i && output_valid && output_ready && !output_last) begin
                // Continue from same source
                fifo_pop[current_source] = 1'b1;
                output_data <= fifo_dout[current_source];
                output_last <= fifo_dout[current_source][DATA_WIDTH-1];
                output_valid <= 1'b1;
            end
        end
    end
    
    //============================================================================
    // ATID Generation
    //============================================================================
    // ATID format: [3:0] = source ID, [7:4] = trace type
    assign output_atid = {4'b0000, current_source[3:0]};
    
    //============================================================================
    // Output Assignments
    //============================================================================
    assign agg_atid_o    = output_atid;
    assign agg_atvalid_o = output_valid;
    assign agg_atdata_o  = output_data;
    assign agg_atlast_o  = output_last;
    assign output_ready  = agg_atready_i;
    
    //============================================================================
    // Assertions
    //============================================================================
    initial begin
        if (NUM_ETMS < 1) begin
            $error("NUM_ETMS must be at least 1");
        end
    end
    
    // Valid signal should not assert without grant
    assert property (@(posedge clk_i) disable iff (!rst_ni)
        agg_atvalid_i |-> grant != '0)
        else $warning("ATVALID without grant");
    
endmodule

//==============================================================================
// Internal module: Synchronous FIFO (copied for completeness)
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
    
    always_ff @(posedge clk_i) begin
        if (wr_en_i) begin
            mem[wr_ptr[PTR_WIDTH-1:0]] <= wr_data_i;
        end
    end
    
    assign rd_data_o = mem[rd_ptr[PTR_WIDTH-1:0]];
    
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            wr_ptr <= '0;
            rd_ptr <= '0;
        end else begin
            if (wr_en_i) wr_ptr <= wr_ptr + 1;
            if (rd_en_i) rd_ptr <= rd_ptr + 1;
        end
    end
    
    assign full_o  = (wr_ptr[PTR_WIDTH] != rd_ptr[PTR_WIDTH]) && 
                     (wr_ptr[PTR_WIDTH-1:0] == rd_ptr[PTR_WIDTH-1:0]);
    assign empty_o = (wr_ptr == rd_ptr);
    
endmodule
