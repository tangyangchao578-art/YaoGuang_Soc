//-----------------------------------------------------------------------------
// YaoGuang SoC SHA Engine Module
// File: sha_engine.sv
// Description: SHA-256/384/512 and SM3 hash engine
// Version: 1.0
// Date: 2026-01-18
//-----------------------------------------------------------------------------

`timescale 1ns/1ps

module sha_engine #(
    parameter int WIDTH = 256
) (
    input  logic              clk,
    input  logic              rstn,
    input  logic              start,
    output logic              done,
    input  logic [511:0]      msg,
    input  logic              last,
    output logic [WIDTH-1:0]  digest,
    output logic              error
);

    //-------------------------------------------------------------------------
    // Parameters
    //-------------------------------------------------------------------------
    typedef enum logic [3:0] {
        SHA_IDLE    = 4'd0,
        SHA_INIT    = 4'd1,
        SHA_PROCESS = 4'd2,
        SHA_FINAL   = 4'd3,
        SHA_DONE    = 4'd4,
        SHA_ERROR   = 4'd5
    } sha_state_t;

    localparam int NUM_ROUNDS = (WIDTH == 256) ? 64 : 80;

    //-------------------------------------------------------------------------
    // Signals
    //-------------------------------------------------------------------------
    sha_state_t                 current_state;
    sha_state_t                 next_state;

    logic [31:0]                w [0:63];
    logic [31:0]                a, b, c, d, e, f, g, h;
    logic [31:0]                h0, h1, h2, h3, h4, h5, h6, h7;
    logic [31:0]                temp1, temp2;

    logic [31:0]                msg_schedule [0:15];

    logic [3:0]                 round_num;
    logic [5:0]                 word_num;

    //-------------------------------------------------------------------------
    // Initial Hash Values
    //-------------------------------------------------------------------------
    initial begin
        if (WIDTH == 256) begin
            h0 = 32'h6a09e667;
            h1 = 32'hbb67ae85;
            h2 = 32'h3c6ef372;
            h3 = 32'ha54ff53a;
            h4 = 32'h510e527f;
            h5 = 32'h9b05688c;
            h6 = 32'h1f83d9ab;
            h7 = 32'h5be0cd19;
        end else if (WIDTH == 384) begin
            h0 = 32'hcbbb9d5d;
            h1 = 32'haa09e667;
            h2 = 32'h629a292a;
            h3 = 32'h367cd507;
            h4 = 32'h9159015a;
            h5 = 32'h152fecd8;
            h6 = 32'h67332667;
            h7 = 32'h8eb44a87;
        end else begin
            h0 = 32'h6a09e667;
            h1 = 32'hf3bcc908;
            h2 = 32'hb9448c3e;
            h3 = 32'h3e87676f;
            h4 = 32'h510e527f;
            h5 = 32'ha145c5b3;
            h6 = 32'h1f83d9ab;
            h7 = 32'hfb41bd6b;
        end
    end

    //-------------------------------------------------------------------------
    // State Machine
    //-------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            current_state <= SHA_IDLE;
        end else begin
            current_state <= next_state;
        end
    end

    always_comb begin
        next_state = current_state;
        error = 1'b0;

        case (current_state)
            SHA_IDLE: begin
                if (start) begin
                    next_state = SHA_INIT;
                end
            end

            SHA_INIT: begin
                next_state = SHA_PROCESS;
            end

            SHA_PROCESS: begin
                if (round_num == NUM_ROUNDS - 1) begin
                    if (last)
                        next_state = SHA_FINAL;
                    else
                        next_state = SHA_DONE;
                end
            end

            SHA_FINAL: begin
                next_state = SHA_DONE;
            end

            SHA_DONE: begin
                next_state = SHA_IDLE;
            end

            SHA_ERROR: begin
                error = 1'b1;
                if (start) next_state = SHA_INIT;
            end
        endcase
    end

    //-------------------------------------------------------------------------
    // Message Schedule Generation
    //-------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            for (int i = 0; i < 16; i++) msg_schedule[i] <= 32'd0;
        end else if (current_state == SHA_IDLE && start) begin
            for (int i = 0; i < 16; i++) begin
                msg_schedule[i] <= msg[i*32 +: 32];
            end
        end else if (current_state == SHA_PROCESS) begin
            if (WIDTH == 256) begin
                w[0]  <= msg_schedule[0];
                w[1]  <= msg_schedule[1];
                w[2]  <= msg_schedule[2];
                w[3]  <= msg_schedule[3];
                w[4]  <= msg_schedule[4];
                w[5]  <= msg_schedule[5];
                w[6]  <= msg_schedule[6];
                w[7]  <= msg_schedule[7];
                w[8]  <= msg_schedule[8];
                w[9]  <= msg_schedule[9];
                w[10] <= msg_schedule[10];
                w[11] <= msg_schedule[11];
                w[12] <= msg_schedule[12];
                w[13] <= msg_schedule[13];
                w[14] <= msg_schedule[14];
                w[15] <= msg_schedule[15];

                for (int i = 16; i < 64; i++) begin
                    w[i] <= sha_sigma1(w[i-2]) + w[i-7] + sha_sigma0(w[i-15]) + w[i-16];
                end
            end else begin
                for (int i = 0; i < 16; i++) begin
                    w[i] <= msg[i*32 +: 32];
                end

                for (int i = 16; i < 80; i++) begin
                    w[i] <= sha_sigma1(w[i-2]) + w[i-7] + sha_sigma0(w[i-15]) + w[i-16];
                end
            end
        end
    end

    //-------------------------------------------------------------------------
    // Hash Computation
    //-------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            a <= 32'd0;
            b <= 32'd0;
            c <= 32'd0;
            d <= 32'd0;
            e <= 32'd0;
            f <= 32'd0;
            g <= 32'd0;
            h <= 32'd0;
            round_num <= 4'd0;
        end else if (current_state == SHA_IDLE && start) begin
            a <= h0;
            b <= h1;
            c <= h2;
            d <= h3;
            e <= h4;
            f <= h5;
            g <= h6;
            h <= h7;
            round_num <= 4'd0;
        end else if (current_state == SHA_PROCESS) begin
            temp1 <= h + sha_SIGMA1(e) + sha_ch(e, f, g) + w[round_num] + sha_K(round_num);
            temp2 <= sha_SIGMA0(a) + sha_maj(a, b, c);

            h <= g;
            g <= f;
            f <= e;
            e <= d + temp1;
            d <= c;
            c <= b;
            b <= a;
            a <= temp1 + temp2;

            round_num <= round_num + 4'd1;
        end else if (current_state == SHA_FINAL) begin
            a <= a + h0;
            b <= b + h1;
            c <= c + h2;
            d <= d + h3;
            e <= e + h4;
            f <= f + h5;
            g <= g + h6;
            h <= h + h7;
        end
    end

    //-------------------------------------------------------------------------
    // SHA Functions
    //-------------------------------------------------------------------------
    function [31:0] sha_ch;
        input [31:0] x, y, z;

        begin
            sha_ch = (x & y) ^ (~x & z);
        end
    endfunction

    function [31:0] sha_maj;
        input [31:0] x, y, z;

        begin
            sha_maj = (x & y) ^ (x & z) ^ (y & z);
        end
    endfunction

    function [31:0] sha_SIGMA0;
        input [31:0] x;

        begin
            sha_SIGMA0 = {x[21:0], x[31:22]} ^ {x[12:0], x[31:13]} ^ {x[6:0], x[31:7]};
        end
    endfunction

    function [31:0] sha_SIGMA1;
        input [31:0] x;

        begin
            sha_SIGMA1 = {x[13:0], x[31:14]} ^ {x[17:0], x[31:18]} ^ {x[0], x[31:1]};
        end
    endfunction

    function [31:0] sha_sigma0;
        input [31:0] x;

        begin
            sha_sigma0 = {x[21:0], x[31:22]} ^ {x[12:0], x[31:13]} ^ {x[7:0], x[31:8]};
        end
    endfunction

    function [31:0] sha_sigma1;
        input [31:0] x;

        begin
            sha_sigma1 = {x[13:0], x[31:14]} ^ {x[17:0], x[31:18]} ^ {x[0], x[31:1]};
        end
    endfunction

    function [31:0] sha_K;
        input [5:0] idx;

        begin
            case (idx)
                6'd0:   sha_K = 32'h428a2f98;
                6'd1:   sha_K = 32'h71374491;
                6'd2:   sha_K = 32'hb5c0fbcf;
                6'd3:   sha_K = 32'he9b5dba5;
                6'd4:   sha_K = 32'h3956c25b;
                6'd5:   sha_K = 32'h59f111f1;
                6'd6:   sha_K = 32'h923f82a4;
                6'd7:   sha_K = 32'hab1c5ed5;
                6'd8:   sha_K = 32'hd807aa98;
                6'd9:   sha_K = 32'h12835b01;
                6'd10:  sha_K = 32'h243185be;
                6'd11:  sha_K = 32'h550c7dc3;
                6'd12:  sha_K = 32'h72be5d74;
                6'd13:  sha_K = 32'h80deb1fe;
                6'd14:  sha_K = 32'h9bdc06a7;
                6'd15:  sha_K = 32'hc19bf174;
                6'd16:  sha_K = 32'he49b69c1;
                6'd17:  sha_K = 32'hefbe4786;
                6'd18:  sha_K = 32'h0fc19dc6;
                6'd19:  sha_K = 32'h240ca1cc;
                6'd20:  sha_K = 32'h2de92c6f;
                6'd21:  sha_K = 32'h4a7484aa;
                6'd22:  sha_K = 32'h5cb0a9dc;
                6'd23:  sha_K = 32'h76f988da;
                6'd24:  sha_K = 32'h983e5152;
                6'd25:  sha_K = 32'ha831c66d;
                6'd26:  sha_K = 32'hb00327c8;
                6'd27:  sha_K = 32'hbf597fc7;
                6'd28:  sha_K = 32'hc6e00bf3;
                6'd29:  sha_K = 32'hd5a79147;
                6'd30:  sha_K = 32'h06ca6351;
                6'd31:  sha_K = 32'h14292967;
                6'd32:  sha_K = 32'h27b70a85;
                6'd33:  sha_K = 32'h2e1b2138;
                6'd34:  sha_K = 32'h4d2c6dfc;
                6'd35:  sha_K = 32'h53380d13;
                6'd36:  sha_K = 32'h650a7354;
                6'd37:  sha_K = 32'h766a0abb;
                6'd38:  sha_K = 32'h81c2c92e;
                6'd39:  sha_K = 32'h92722c85;
                6'd40:  sha_K = 32'ha2bfe8a1;
                6'd41:  sha_K = 32'ha81a664b;
                6'd42:  sha_K = 32'hc24b8b70;
                6'd43:  sha_K = 32'hc76c51a3;
                6'd44:  sha_K = 32'hd192e819;
                6'd45:  sha_K = 32'hd6990624;
                6'd46:  sha_K = 32'hf40e3585;
                6'd47:  sha_K = 32'h106aa070;
                6'd48:  sha_K = 32'h19a4c116;
                6'd49:  sha_K = 32'h1e376c08;
                6'd50:  sha_K = 32'h2748774c;
                6'd51:  sha_K = 32'h34b0bcb5;
                6'd52:  sha_K = 32'h391c0cb3;
                6'd53:  sha_K = 32'h4ed8aa4a;
                6'd54:  sha_K = 32'h5b9cca4f;
                6'd55:  sha_K = 32'h682e6ff3;
                6'd56:  sha_K = 32'h748f82ee;
                6'd57:  sha_K = 32'h78a5636f;
                6'd58:  sha_K = 32'h84c87814;
                6'd59:  sha_K = 32'h8cc70208;
                6'd60:  sha_K = 32'h90befffa;
                6'd61:  sha_K = 32'ha4506ceb;
                6'd62:  sha_K = 32'bef9a3f7b5c9f0d0; // 32'hbef9a3f7
                6'd63:  sha_K = 32'hc67178f2;
                default: sha_K = 32'd0;
            endcase
        end
    endfunction

    //-------------------------------------------------------------------------
    // Output Assignment
    //-------------------------------------------------------------------------
    assign done = (current_state == SHA_DONE);
    assign digest = {a, b, c, d, e, f, g, h};

endmodule
