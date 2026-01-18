//-----------------------------------------------------------------------------
// YaoGuang SoC True Random Number Generator
// File: trng.sv
// Description: Entropy source and DRBG for cryptographic random numbers
// Version: 1.0
// Date: 2026-01-18
//-----------------------------------------------------------------------------

`timescale 1ns/1ps

module trng #(
    parameter int WIDTH = 32,
    parameter int FIFO_DEPTH = 32
) (
    input  logic              clk,
    input  logic              rstn,
    input  logic              enable,
    output logic              done,
    output logic [WIDTH-1:0]  entropy_out,
    output logic              ready
);

    //-------------------------------------------------------------------------
    // Parameters
    //-------------------------------------------------------------------------
    typedef enum logic [3:0] {
        TRNG_IDLE     = 4'd0,
        TRNG_ENTROPY  = 4'd1,
        TRNG_DEBIAS   = 4'd2,
        TRNG_EXTRACT  = 4'd3,
        TRNG_TEST     = 4'd4,
        TRNG_DONE     = 4'd5,
        TRNG_ERROR    = 4'd6
    } trng_state_t;

    localparam int ENTROPY_WIDTH = 128;

    //-------------------------------------------------------------------------
    // Signals
    //-------------------------------------------------------------------------
    trng_state_t                 current_state;
    trng_state_t                 next_state;

    logic [7:0]                  ro_count [0:7];
    logic [7:0]                  ro_sample [0:7];
    logic [ENTROPY_WIDTH-1:0]    raw_entropy;

    logic [31:0]                 debiased_data;
    logic [7:0]                  von_neumann_bits [0:3];

    logic [31:0]                 hash_input;
    logic [255:0]                hash_output;

    logic [$clog2(FIFO_DEPTH):0] fifo_count;
    logic [31:0]                 fifo_data [FIFO_DEPTH-1:0];
    logic [$clog2(FIFO_DEPTH)-1:0] fifo_wr_ptr;
    logic [$clog2(FIFO_DEPTH)-1:0] fifo_rd_ptr;

    logic                        ro_clk;
    logic [15:0]                 ro_divider;
    logic                        ro_enable;

    //-------------------------------------------------------------------------
    // Ring Oscillator Entropy Source
    //-------------------------------------------------------------------------
    assign ro_clk = ro_enable;

    always_ff @(posedge ro_clk) begin
        ro_divider <= ro_divider + 16'd1;
    end

    always_ff @(posedge clk) begin
        if (enable) begin
            ro_enable <= 1'b1;
        end else begin
            ro_enable <= 1'b0;
        end
    end

    // Generate multiple ring oscillators
    genvar osc_idx;
    generate
        for (osc_idx = 0; osc_idx < 8; osc_idx++) begin : ro_gen
            ring_osc #(
                .INVERTERS(osc_idx + 3)
            ) ro_inst (
                .enable(ro_enable),
                .out(ro_sample[osc_idx])
            );
        end
    endgenerate

    //-------------------------------------------------------------------------
    // Entropy Collection
    //-------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            for (int i = 0; i < 8; i++) ro_count[i] <= 8'd0;
            raw_entropy <= 128'd0;
        end else if (enable) begin
            ro_count[0] <= ro_count[0] + ro_sample[0];
            ro_count[1] <= ro_count[1] + ro_sample[1];
            ro_count[2] <= ro_count[2] + ro_sample[2];
            ro_count[3] <= ro_count[3] + ro_sample[3];
            ro_count[4] <= ro_count[4] + ro_sample[4];
            ro_count[5] <= ro_count[5] + ro_sample[5];
            ro_count[6] <= ro_count[6] + ro_sample[6];
            ro_count[7] <= ro_count[7] + ro_sample[7];

            if (&ro_divider) begin
                raw_entropy <= {ro_count[0], ro_count[1], ro_count[2], ro_count[3],
                               ro_count[4], ro_count[5], ro_count[6], ro_count[7],
                               ro_count[0], ro_count[1], ro_count[2], ro_count[3],
                               ro_count[4], ro_count[5], ro_count[6], ro_count[7]};
            end
        end
    end

    //-------------------------------------------------------------------------
    // Von Neumann De-biasing
    //-------------------------------------------------------------------------
    always_comb begin
        von_neumann_bits[0] = {raw_entropy[7], raw_entropy[6]};
        von_neumann_bits[1] = {raw_entropy[15], raw_entropy[14]};
        von_neumann_bits[2] = {raw_entropy[23], raw_entropy[22]};
        von_neumann_bits[3] = {raw_entropy[31], raw_entropy[30]};

        debiased_data = 32'd0;

        if (von_neumann_bits[0] == 2'b01)
            debiased_data[0] = 1'b1;
        else if (von_neumann_bits[0] == 2'b10)
            debiased_data[0] = 1'b0;

        if (von_neumann_bits[1] == 2'b01)
            debiased_data[1] = 1'b1;
        else if (von_neumann_bits[1] == 2'b10)
            debiased_data[1] = 1'b0;

        if (von_neumann_bits[2] == 2'b01)
            debiased_data[2] = 1'b1;
        else if (von_neumann_bits[2] == 2'b10)
            debiased_data[2] = 1'b0;

        if (von_neumann_bits[3] == 2'b01)
            debiased_data[3] = 1'b1;
        else if (von_neumann_bits[3] == 2'b10)
            debiased_data[3] = 1'b0;
    end

    //-------------------------------------------------------------------------
    // SHA-256 Entropy Extractor
    //-------------------------------------------------------------------------
    sha_engine #(
        .WIDTH(256)
    ) sha_inst (
        .clk(clk),
        .rstn(rstn),
        .start(current_state == TRNG_EXTRACT),
        .done(),
        .msg({raw_entropy, 384'd0}),
        .last(1'b1),
        .digest(hash_output),
        .error()
    );

    //-------------------------------------------------------------------------
    // FIFO Buffer
    //-------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            fifo_count <= 'd0;
            fifo_wr_ptr <= 'd0;
            fifo_rd_ptr <= 'd0;
        end else begin
            case (current_state)
                TRNG_EXTRACT: begin
                    if (fifo_count < FIFO_DEPTH) begin
                        fifo_data[fifo_wr_ptr] <= hash_output[31:0];
                        fifo_wr_ptr <= fifo_wr_ptr + 1'b1;
                        fifo_count <= fifo_count + 1'b1;
                    end
                end

                TRNG_DONE: begin
                    if (fifo_count > 0) begin
                        entropy_out <= fifo_data[fifo_rd_ptr];
                        fifo_rd_ptr <= fifo_rd_ptr + 1'b1;
                        fifo_count <= fifo_count - 1'b1;
                    end
                end
            endcase
        end
    end

    //-------------------------------------------------------------------------
    // State Machine
    //-------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            current_state <= TRNG_IDLE;
        end else begin
            current_state <= next_state;
        end
    end

    always_comb begin
        next_state = current_state;

        case (current_state)
            TRNG_IDLE: begin
                if (enable) begin
                    next_state = TRNG_ENTROPY;
                end
            end

            TRNG_ENTROPY: begin
                if (&ro_divider) begin
                    next_state = TRNG_DEBIAS;
                end
            end

            TRNG_DEBIAS: begin
                next_state = TRNG_EXTRACT;
            end

            TRNG_EXTRACT: begin
                if (fifo_count >= FIFO_DEPTH)
                    next_state = TRNG_TEST;
            end

            TRNG_TEST: begin
                next_state = TRNG_DONE;
            end

            TRNG_DONE: begin
                if (fifo_count == 0)
                    next_state = TRNG_IDLE;
            end

            TRNG_ERROR: begin
                next_state = TRNG_IDLE;
            end
        endcase
    end

    //-------------------------------------------------------------------------
    // Health Test (Simple repetition test)
    //-------------------------------------------------------------------------
    logic [31:0]                 last_sample;
    logic [5:0]                  repeat_count;
    logic                        health_fail;

    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            last_sample <= 32'd0;
            repeat_count <= 6'd0;
            health_fail <= 1'b0;
        end else if (current_state == TRNG_ENTROPY) begin
            if (&ro_divider) begin
                if (raw_entropy[31:0] == last_sample) begin
                    repeat_count <= repeat_count + 6'd1;
                    if (repeat_count > 6'd32) begin
                        health_fail <= 1'b1;
                    end
                end else begin
                    last_sample <= raw_entropy[31:0];
                    repeat_count <= 6'd0;
                end
            end
        end
    end

    //-------------------------------------------------------------------------
    // Output Assignment
    //-------------------------------------------------------------------------
    assign done = (current_state == TRNG_DONE);
    assign ready = (fifo_count > 0);

endmodule

//-----------------------------------------------------------------------------
// Ring Oscillator Sub-module
//-----------------------------------------------------------------------------
module ring_osc #(
    parameter int INVERTERS = 5
) (
    input  logic enable,
    output logic out
);

    logic [INVERTERS-1:0] stage;

    always_ff @(posedge out) begin
        if (enable) begin
            stage <= ~stage;
        end
    end

    assign out = stage[INVERTERS-1];

endmodule
