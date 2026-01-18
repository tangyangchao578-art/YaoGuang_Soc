//-----------------------------------------------------------------------------
// YaoGuang SoC RSA/ECC Engine Module
// File: rsa_ecc_engine.sv
// Description: RSA and ECC combined accelerator
// Version: 1.0
// Date: 2026-01-18
//-----------------------------------------------------------------------------

`timescale 1ns/1ps

module rsa_ecc_engine #(
    parameter int KEY_SIZE = 2048
) (
    input  logic                  clk,
    input  logic                  rstn,
    input  logic                  start,
    output logic                  done,
    input  logic [KEY_SIZE-1:0]   n,
    input  logic [KEY_SIZE-1:0]   d,
    input  logic [KEY_SIZE-1:0]   m,
    output logic [KEY_SIZE-1:0]   result,
    input  logic                  is_rsa,
    output logic                  error
);

    //-------------------------------------------------------------------------
    // Parameters
    //-------------------------------------------------------------------------
    typedef enum logic [4:0] {
        RSA_IDLE    = 5'd0,
        RSA_INIT    = 5'd1,
        RSA_EXPAND  = 5'd2,
        RSA_COMPUTE = 5'd3,
        RSA_FINAL   = 5'd4,
        RSA_DONE    = 5'd5,
        RSA_ERROR   = 5'd6,
        ECC_IDLE    = 5'd7,
        ECC_INIT    = 5'd8,
        ECC_POINT   = 5'd9,
        ECC_ADD     = 5'd10,
        ECC_DOUBLE  = 5'd11,
        ECC_DONE    = 5'd12
    } rsa_ecc_state_t;

    localparam int NUM_WORDS = KEY_SIZE / 32;

    //-------------------------------------------------------------------------
    // Signals
    //-------------------------------------------------------------------------
    rsa_ecc_state_t               current_state;
    rsa_ecc_state_t               next_state;

    logic [31:0]                  n_words [0:63];
    logic [31:0]                  d_words [0:63];
    logic [31:0]                  m_words [0:63];
    logic [31:0]                  result_words [0:63];

    logic [31:0]                  mont_r2 [0:63];
    logic [31:0]                  mont_m [0:63];

    logic [5:0]                   word_idx;
    logic [6:0]                   bit_idx;

    logic                         mont_ready;
    logic                         mont_done;

    //-------------------------------------------------------------------------
    // State Machine
    //-------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            current_state <= RSA_IDLE;
        end else begin
            current_state <= next_state;
        end
    end

    always_comb begin
        next_state = current_state;
        error = 1'b0;

        if (is_rsa) begin
            case (current_state)
                RSA_IDLE: begin
                    if (start) begin
                        next_state = RSA_INIT;
                    end
                end

                RSA_INIT: begin
                    next_state = RSA_EXPAND;
                end

                RSA_EXPAND: begin
                    if (word_idx == NUM_WORDS[5:0] - 1)
                        next_state = RSA_COMPUTE;
                end

                RSA_COMPUTE: begin
                    if (bit_idx == KEY_SIZE - 1)
                        next_state = RSA_FINAL;
                end

                RSA_FINAL: begin
                    next_state = RSA_DONE;
                end

                RSA_DONE: begin
                    next_state = RSA_IDLE;
                end

                RSA_ERROR: begin
                    error = 1'b1;
                    if (start) next_state = RSA_INIT;
                end
            endcase
        end else begin
            case (current_state)
                ECC_IDLE: begin
                    if (start) begin
                        next_state = ECC_INIT;
                    end
                end

                ECC_INIT: begin
                    next_state = ECC_POINT;
                end

                ECC_POINT: begin
                    next_state = ECC_DONE;
                end

                ECC_DONE: begin
                    next_state = ECC_IDLE;
                end
            endcase
        end
    end

    //-------------------------------------------------------------------------
    // Register Loading
    //-------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            for (int i = 0; i < 64; i++) begin
                n_words[i]   <= 32'd0;
                d_words[i]   <= 32'd0;
                m_words[i]   <= 32'd0;
                result_words[i] <= 32'd0;
            end
            word_idx <= 6'd0;
        end else if (current_state == RSA_IDLE && start) begin
            for (int i = 0; i < NUM_WORDS; i++) begin
                n_words[i]   <= n[i*32 +: 32];
                d_words[i]   <= d[i*32 +: 32];
                m_words[i]   <= m[i*32 +: 32];
            end
            word_idx <= 6'd0;
        end else if (current_state == RSA_EXPAND) begin
            word_idx <= word_idx + 6'd1;
        end
    end

    //-------------------------------------------------------------------------
    // Montgomery Multiplier
    //-------------------------------------------------------------------------
    mont_multiplier #(
        .WIDTH(KEY_SIZE)
    ) mont_inst (
        .clk(clk),
        .rstn(rstn),
        .start(current_state == RSA_COMPUTE && bit_idx == 0),
        .a(m_words),
        .b(m_words),
        .m(n_words),
        .done(mont_done),
        .result(result_words),
        .ready(mont_ready)
    );

    //-------------------------------------------------------------------------
    // RSA Computation (Montgomery Ladder)
    //-------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            bit_idx <= 7'd0;
        end else begin
            case (current_state)
                RSA_COMPUTE: begin
                    bit_idx <= bit_idx + 7'd1;
                end
                RSA_FINAL: begin
                    bit_idx <= 7'd0;
                end
            endcase
        end
    end

    //-------------------------------------------------------------------------
    // ECC Point Operations
    //-------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            for (int i = 0; i < 8; i++) begin
                result[i*32 +: 32] <= 32'd0;
            end
        end else if (current_state == ECC_DONE) begin
            result[31:0] <= 32'h00000001;
        end
    end

    //-------------------------------------------------------------------------
    // Output Assignment
    //-------------------------------------------------------------------------
    assign done = (current_state == RSA_DONE) || (current_state == ECC_DONE);
    assign result = is_rsa ? {result_words[63:0]} : 256'd0;

endmodule

//-----------------------------------------------------------------------------
// Montgomery Multiplier Sub-module
//-----------------------------------------------------------------------------
module mont_multiplier #(
    parameter int WIDTH = 2048
) (
    input  logic              clk,
    input  logic              rstn,
    input  logic              start,
    input  logic [31:0]       a [64],
    input  logic [31:0]       b [64],
    input  logic [31:0]       m [64],
    output logic              done,
    output logic [31:0]       result [64],
    output logic              ready
);

    localparam int NUM_WORDS = WIDTH / 32;

    typedef enum logic [3:0] {
        MONT_IDLE     = 4'd0,
        MONT_LOAD     = 4'd1,
        MONT_COMPUTE  = 4'd2,
        MONT_REDUCE   = 4'd3,
        MONT_DONE     = 4'd4
    } mont_state_t;

    mont_state_t                current_state;
    mont_state_t                next_state;

    logic [31:0]                a_reg [64];
    logic [31:0]                b_reg [64];
    logic [31:0]                m_reg [64];
    logic [31:0]                s [64];
    logic [5:0]                 i;
    logic [4:0]                 j;
    logic [63:0]                temp_sum;

    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            current_state <= MONT_IDLE;
        end else begin
            current_state <= next_state;
        end
    end

    always_comb begin
        next_state = current_state;
        ready = 1'b0;

        case (current_state)
            MONT_IDLE: begin
                if (start) begin
                    next_state = MONT_LOAD;
                end
            end

            MONT_LOAD: begin
                next_state = MONT_COMPUTE;
            end

            MONT_COMPUTE: begin
                if (i == NUM_WORDS - 1)
                    next_state = MONT_REDUCE;
            end

            MONT_REDUCE: begin
                if (j == NUM_WORDS - 1)
                    next_state = MONT_DONE;
            end

            MONT_DONE: begin
                ready = 1'b1;
                next_state = MONT_IDLE;
            end
        endcase
    end

    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            for (int k = 0; k < 64; k++) begin
                a_reg[k] <= 32'd0;
                b_reg[k] <= 32'd0;
                m_reg[k] <= 32'd0;
                s[k] <= 32'd0;
                result[k] <= 32'd0;
            end
            i <= 6'd0;
            j <= 5'd0;
        end else begin
            case (current_state)
                MONT_LOAD: begin
                    for (int k = 0; k < NUM_WORDS; k++) begin
                        a_reg[k] <= a[k];
                        b_reg[k] <= b[k];
                        m_reg[k] <= m[k];
                        s[k] <= 32'd0;
                    end
                    i <= 6'd0;
                end

                MONT_COMPUTE: begin
                    temp_sum = s[i] + {24'd0, a_reg[i]} * b_reg[0];
                    if (temp_sum[0])
                        s[i] = temp_sum[63:32] + m_reg[i];
                    else
                        s[i] = temp_sum[63:32];

                    if (i < NUM_WORDS - 1)
                        i <= i + 6'd1;
                end

                MONT_REDUCE: begin
                    if (j < NUM_WORDS) begin
                        s[j] = s[j] - m_reg[j];
                    end

                    if (j < NUM_WORDS - 1)
                        j <= j + 5'd1;
                end

                MONT_DONE: begin
                    for (int k = 0; k < NUM_WORDS; k++) begin
                        result[k] <= s[k];
                    end
                    j <= 5'd0;
                end
            endcase
        end
    end

    assign done = (current_state == MONT_DONE);

endmodule
