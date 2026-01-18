//-----------------------------------------------------------------------------
// YaoGuang SoC SM4 Engine Module
// File: sm4_engine.sv
// Description: SM4 block cipher engine
// Version: 1.0
// Date: 2026-01-18
//-----------------------------------------------------------------------------

`timescale 1ns/1ps

module sm4_engine #(
    parameter int KEY_WIDTH = 128
) (
    input  logic              clk,
    input  logic              rstn,
    input  logic              start,
    output logic              done,
    input  logic [KEY_WIDTH-1:0] key,
    input  logic [127:0]      iv,
    input  logic [127:0]      input_data,
    output logic [127:0]      output_data,
    input  logic [1:0]        mode,
    output logic              error
);

    //-------------------------------------------------------------------------
    // Parameters
    //-------------------------------------------------------------------------
    typedef enum logic [3:0] {
        SM4_IDLE     = 4'd0,
        SM4_KEY_EXP  = 4'd1,
        SM4_ROUND_0  = 4'd2,
        SM4_ROUND_N  = 4'd3,
        SM4_FINAL    = 4'd4,
        SM4_DONE     = 4'd5,
        SM4_ERROR    = 4'd6
    } sm4_state_t;

    localparam int NUM_ROUNDS = 32;

    //-------------------------------------------------------------------------
    // Signals
    //-------------------------------------------------------------------------
    sm4_state_t                  current_state;
    sm4_state_t                  next_state;

    logic [31:0]                 round_key [0:31];
    logic [31:0]                 state_reg;
    logic [31:0]                 next_state_reg;

    logic [4:0]                  round_num;
    logic [4:0]                  next_round_num;

    //-------------------------------------------------------------------------
    // SM4 S-Box
    //-------------------------------------------------------------------------
    logic [7:0] sm4_sbox [0:255];

    initial begin
        sm4_sbox[0]   = 8'hd6; sm4_sbox[1]   = 8'h90; sm4_sbox[2]   = 8'he9; sm4_sbox[3]   = 8'hfe;
        sm4_sbox[4]   = 8'hcc; sm4_sbox[5]   = 8'he1; sm4_sbox[6]   = 8'h73; sm4_sbox[7]   = 8'h84;
        sm4_sbox[8]   = 8'hc5; sm4_sbox[9]   = 8'h7f; sm4_sbox[10]  = 8'h3c; sm4_sbox[11]  = 8'h82;
        sm4_sbox[12]  = 8'h77; sm4_sbox[13]  = 8'h83; sm4_sbox[14]  = 8'h8f; sm4_sbox[15]  = 8'h85;
        sm4_sbox[16]  = 8'hc8; sm4_sbox[17]  = 8'ha8; sm4_sbox[18]  = 8'h96; sm4_sbox[19]  = 8'h56;
        sm4_sbox[20]  = 8'h11; sm4_sbox[21]  = 8'h44; sm4_sbox[22]  = 8'h45; sm4_sbox[23]  = 8'h92;
        sm4_sbox[24]  = 8'hce; sm4_sbox[25]  = 8'h7e; sm4_sbox[26]  = 8'h38; sm4_sbox[27]  = 8'hd0;
        sm4_sbox[28]  = 8'h48; sm4_sbox[29]  = 8'hc7; sm4_sbox[30]  = 8'ha1; sm4_sbox[31]  = 8'h54;
        sm4_sbox[32]  = 8'h37; sm4_sbox[33]  = 8'hc2; sm4_sbox[34]  = 8'h32; sm4_sbox[35]  = 8'h9b;
        sm4_sbox[36]  = 8'h64; sm4_sbox[37]  = 8'h01; sm4_sbox[38]  = 8'h55; sm4_sbox[39]  = 8'had;
        sm4_sbox[40]  = 8'h13; sm4_sbox[41]  = 8'h54; sm4_sbox[42]  = 8'hbf; sm4_sbox[43]  = 8'h41;
        sm4_sbox[44]  = 8'h6a; sm4_sbox[45]  = 8'h71; sm4_sbox[46]  = 8'h89; sm4_sbox[47]  = 8'h42;
        sm4_sbox[48]  = 8'h8b; sm4_sbox[49]  = 8'he7; sm4_sbox[50]  = 8'h55; sm4_sbox[51]  = 8'hbd;
        sm4_sbox[52]  = 8'h06; sm4_sbox[53]  = 8'h7a; sm4_sbox[54]  = 8'ha9; sm4_sbox[55]  = 8'hfa;
        sm4_sbox[56]  = 8'h30; sm4_sbox[57]  = 8'h81; sm4_sbox[58]  = 8'hc2; sm4_sbox[59]  = 8'ha9;
        sm4_sbox[60]  = 8'he0; sm4_sbox[61]  = 8'haa; sm4_sbox[62]  = 8'h3f; sm4_sbox[63]  = 8'had;
        sm4_sbox[64]  = 8'h4e; sm4_sbox[65]  = 8'ha6; sm4_sbox[66]  = 8'hcc; sm4_sbox[67]  = 8'hc5;
        sm4_sbox[68]  = 8'h30; sm4_sbox[69]  = 8'h1c; sm4_sbox[70]  = 8'ha8; sm4_sbox[71]  = 8'hed;
        sm4_sbox[72]  = 8'h1d; sm4_sbox[73]  = 8'h16; sm4_sbox[74]  = 8'hf8; sm4_sbox[75]  = 8'h97;
        sm4_sbox[76]  = 8'hff; sm4_sbox[77]  = 8'hff; sm4_sbox[78]  = 8'h00; sm4_sbox[79]  = 8'h00;
        sm4_sbox[80]  = 8'h00; sm4_sbox[81]  = 8'h01; sm4_sbox[82]  = 8'h08; sm4_sbox[83]  = 8'h14;
        sm4_sbox[84]  = 8'h64; sm4_sbox[85]  = 8'h3e; sm4_sbox[86]  = 8'h8f; sm4_sbox[87]  = 8'ha9;
        sm4_sbox[88]  = 8'h4c; sm4_sbox[89]  = 8'hda; sm4_sbox[90]  = 8'hd0; sm4_sbox[91]  = 8'h8f;
        sm4_sbox[92]  = 8'h4b; sm4_sbox[93]  = 8'h00; sm4_sbox[94]  = 8'he3; sm4_sbox[95]  = 8'h90;
        sm4_sbox[96]  = 8'h92; sm4_sbox[97]  = 8'h15; sm4_sbox[98]  = 8'h2a; sm4_sbox[99]  = 8'he5;
        sm4_sbox[100] = 8'h77; sm4_sbox[101] = 8'h0f; sm4_sbox[102] = 8'hd7; sm4_sbox[103] = 8'ha2;
        sm4_sbox[104] = 8'h49; sm4_sbox[105] = 8'hf4; sm4_sbox[106] = 8'hc7; sm4_sbox[107] = 8'hba;
        sm4_sbox[108] = 8'h77; sm4_sbox[109] = 8'h2f; sm4_sbox[110] = 8'h6c; sm4_sbox[111] = 8'h15;
        sm4_sbox[112] = 8'h28; sm4_sbox[113] = 8'h2d; sm4_sbox[114] = 8'hf4; sm4_sbox[115] = 8'h6e;
        sm4_sbox[116] = 8'hcf; sm4_sbox[117] = 8'h4d; sm4_sbox[118] = 8'hd5; sm4_sbox[119] = 8'hd0;
        sm4_sbox[120] = 8'h9a; sm4_sbox[121] = 8'hd1; sm4_sbox[122] = 8'h29; sm4_sbox[123] = 8'hd8;
        sm4_sbox[124] = 8'h51; sm4_sbox[125] = 8'h7f; sm4_sbox[126] = 8'ha4; sm4_sbox[127] = 8'h14;
        sm4_sbox[128] = 8'h50; sm4_sbox[129] = 8'h4f; sm4_sbox[130] = 8'hde; sm4_sbox[131] = 8'h5e;
        sm4_sbox[132] = 8'h13; sm4_sbox[133] = 8'ha5; sm4_sbox[134] = 8'h5c; sm4_sbox[135] = 8'h2f;
        sm4_sbox[136] = 8'h9a; sm4_sbox[137] = 8'h5a; sm4_sbox[138] = 8'ha4; sm4_sbox[139] = 8'hf2;
        sm4_sbox[140] = 8'h91; sm4_sbox[141] = 8'h98; sm4_sbox[142] = 8'hd7; sm4_sbox[143] = 8'hbb;
        sm4_sbox[144] = 8'hd3; sm4_sbox[145] = 8'h60; sm4_sbox[146] = 8'h58; sm4_sbox[147] = 8'hec;
        sm4_sbox[148] = 8'hfe; sm4_sbox[149] = 8'h16; sm4_sbox[150] = 8'h2b; sm4_sbox[151] = 8'h69;
        sm4_sbox[152] = 8'h9a; sm4_sbox[153] = 8'h98; sm4_sbox[154] = 8'h2a; sm4_sbox[155] = 8'hfa;
        sm4_sbox[156] = 8'h31; sm4_sbox[157] = 8'ha0; sm4_sbox[158] = 8'h51; sm4_sbox[159] = 8'h57;
        sm4_sbox[160] = 8'hc2; sm4_sbox[161] = 8'h4a; sm4_sbox[162] = 8'hd8; sm4_sbox[163] = 8'h57;
        sm4_sbox[164] = 8'h18; sm4_sbox[165] = 8'h38; sm4_sbox[166] = 8'h19; sm4_sbox[167] = 8'h8e;
        sm4_sbox[168] = 8'he1; sm4_sbox[169] = 8'he2; sm4_sbox[170] = 8'h16; sm4_sbox[171] = 8'h71;
        sm4_sbox[172] = 8'h89; sm4_sbox[173] = 8'hf0; sm4_sbox[174] = 8'h3d; sm4_sbox[175] = 8'h84;
        sm4_sbox[176] = 8'ha0; sm4_sbox[177] = 8'hf0; sm4_sbox[178] = 8'hd3; sm4_sbox[179] = 8'hd5;
        sm4_sbox[180] = 8'hf5; sm4_sbox[181] = 8'hac; sm4_sbox[182] = 8'h11; sm4_sbox[183] = 8'h24;
        sm4_sbox[184] = 8'h41; sm4_sbox[185] = 8'hbd; sm4_sbox[186] = 8'h6e; sm4_sbox[187] = 8'hf1;
        sm4_sbox[188] = 8'hbc; sm4_sbox[189] = 8'h94; sm4_sbox[190] = 8'h6f; sm4_sbox[191] = 8'hab;
        sm4_sbox[192] = 8'h1c; sm4_sbox[193] = 8'h9e; sm4_sbox[194] = 8'hef; sm4_sbox[195] = 8'hab;
        sm4_sbox[196] = 8'ha1; sm4_sbox[197] = 8'hd6; sm4_sbox[198] = 8'h14; sm4_sbox[199] = 8'h29;
        sm4_sbox[200] = 8'h67; sm4_sbox[201] = 8'h3c; sm4_sbox[202] = 8'ha5; sm4_sbox[203] = 8'he4;
        sm4_sbox[204] = 8'h9a; sm4_sbox[205] = 8'h84; sm4_sbox[206] = 8'h58; sm4_sbox[207] = 8'hdd;
        sm4_sbox[208] = 8'h74; sm4_sbox[209] = 8'h1f; sm4_sbox[210] = 8'h04; sm4_sbox[211] = 8'h4b;
        sm4_sbox[212] = 8'h50; sm4_sbox[213] = 8'h18; sm4_sbox[214] = 8'hc5; sm4_sbox[215] = 8'h66;
        sm4_sbox[216] = 8'ha6; sm4_sbox[217] = 8'h41; sm4_sbox[218] = 8'h2e; sm4_sbox[219] = 8'h08;
        sm4_sbox[220] = 8'h17; sm4_sbox[221] = 8'h9e; sm4_sbox[222] = 8'h9f; sm4_sbox[223] = 8'hef;
        sm4_sbox[224] = 8'he3; sm4_sbox[225] = 8'ha5; sm4_sbox[226] = 8'hf3; sm4_sbox[227] = 8'hd6;
        sm4_sbox[228] = 8'hdc; sm4_sbox[229] = 8'h35; sm4_sbox[230] = 8'h92; sm4_sbox[231] = 8'hdc;
        sm4_sbox[232] = 8'he7; sm4_sbox[233] = 8'hc0; sm4_sbox[234] = 8'h5e; sm4_sbox[235] = 8'h84;
        sm4_sbox[236] = 8'hcf; sm4_sbox[237] = 8'he6; sm4_sbox[238] = 8'h94; sm4_sbox[239] = 8'hf9;
        sm4_sbox[240] = 8'h1b; sm4_sbox[241] = 8'h65; sm4_sbox[242] = 8'h5c; sm4_sbox[243] = 8'h13;
        sm4_sbox[244] = 8'h5d; sm4_sbox[245] = 8'hb8; sm4_sbox[246] = 8'h5b; sm4_sbox[247] = 8'ha0;
        sm4_sbox[248] = 8'ha8; sm4_sbox[249] = 8'h57; sm4_sbox[250] = 8'h83; sm4_sbox[251] = 8'he1;
        sm4_sbox[252] = 8'h35; sm4_sbox[253] = 8'h9a; sm4_sbox[254] = 8'h2b; sm4_sbox[255] = 8'h86;
    end

    //-------------------------------------------------------------------------
    // State Machine
    //-------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            current_state <= SM4_IDLE;
        end else begin
            current_state <= next_state;
        end
    end

    always_comb begin
        next_state = current_state;
        error = 1'b0;

        case (current_state)
            SM4_IDLE: begin
                if (start) begin
                    next_state = SM4_KEY_EXP;
                end
            end

            SM4_KEY_EXP: begin
                next_state = SM4_ROUND_0;
            end

            SM4_ROUND_0: begin
                next_state = SM4_ROUND_N;
            end

            SM4_ROUND_N: begin
                if (round_num == NUM_ROUNDS - 1)
                    next_state = SM4_FINAL;
            end

            SM4_FINAL: begin
                next_state = SM4_DONE;
            end

            SM4_DONE: begin
                next_state = SM4_IDLE;
            end

            SM4_ERROR: begin
                error = 1'b1;
                if (start) next_state = SM4_KEY_EXP;
            end
        endcase
    end

    //-------------------------------------------------------------------------
    // Round Counter
    //-------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            round_num <= 5'd0;
        end else begin
            case (current_state)
                SM4_ROUND_0: round_num <= 5'd0;
                SM4_ROUND_N: round_num <= round_num + 5'd1;
            endcase
        end
    end

    //-------------------------------------------------------------------------
    // State Register
    //-------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            state_reg <= 32'd0;
        end else begin
            case (current_state)
                SM4_ROUND_0: begin
                    state_reg <= input_data[127:96];
                end
                SM4_ROUND_N, SM4_FINAL: begin
                    state_reg <= next_state_reg;
                end
            endcase
        end
    end

    //-------------------------------------------------------------------------
    // Key Expansion
    //-------------------------------------------------------------------------
    localparam [31:0] FK [4] = '{32'h0fac34e5, 32'hf87c5bd5, 32'he0bb155e9, 32'hd395746f};
    localparam [31:0] CK [32] = '{
        32'h00070e15, 32'h1c232a31, 32'h383f464d, 32'h545b6269,
        32'h70777e85, 32'h8c939aa1, 32'ha8afb6bd, 32'hc4cbd2d9,
        32'he0e7eef5, 32'hfc030a11, 32'h181d262b, 32'h343f4249,
        32'h505c6067, 32'h6c737c81, 32'h88949e97, 32'ha4b8b8b9,
        32'hc0c7ced5, 32'hdce3eaf1, 32'hf8ff060d, 32'h141b2229,
        32'h30393e45, 32'h4c535c61, 32'h686d7679, 32'h848b9299,
        32'ha0a7aeb5, 32'hbcc3cad9, 32'hd8dfeaf5, 32'hf4fbf20b,
        32'h10171e25, 32'h2c333a41, 32'h484f565d, 32'h646b7079
    };

    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            for (int i = 0; i < 32; i++) round_key[i] <= 32'd0;
        end else if (current_state == SM4_IDLE && start) begin
            for (int i = 0; i < 4; i++) begin
                round_key[i] = key[127 - i*32 -: 32] ^ FK[i];
            end
            for (int i = 0; i < 28; i++) begin
                round_key[i + 4] = sm4_key_update(round_key[i + 3], round_key[i + 2],
                                                  round_key[i + 1], round_key[i], CK[i]);
            end
        end
    end

    function [31:0] sm4_key_update;
        input [31:0] x0, x1, x2, x3;
        input [31:0] ck;

        reg [31:0] t;

        begin
            t = x0 ^ x1 ^ x2 ^ x3 ^ ck;
            t = sm4_sbox_l(t);
            sm4_key_update = t ^ sm4_rotl32(t, 13) ^ sm4_rotl32(t, 23);
        end
    endfunction

    //-------------------------------------------------------------------------
    // Round Function
    //-------------------------------------------------------------------------
    always_comb begin
        next_state_reg = state_reg;

        case (current_state)
            SM4_ROUND_0: begin
                next_state_reg = state_reg;
            end

            SM4_ROUND_N: begin
                next_state_reg = sm4_round_function(state_reg,
                                                    input_data[95:64],
                                                    input_data[63:32],
                                                    input_data[31:0],
                                                    round_key[round_num]);
            end

            SM4_FINAL: begin
                next_state_reg = sm4_round_function(input_data[95:64],
                                                    input_data[63:32],
                                                    input_data[31:0],
                                                    input_data[127:96],
                                                    round_key[round_num]);
            end
        endcase
    end

    function [31:0] sm4_round_function;
        input [31:0] x0, x1, x2, x3;
        input [31:0] rk;

        reg [31:0] t;

        begin
            t = x0 ^ x1 ^ x2 ^ x3 ^ rk;
            t = sm4_sbox_l(t);
            sm4_round_function = t ^ sm4_rotl32(t, 2) ^ sm4_rotl32(t, 10) ^
                                 sm4_rotl32(t, 18) ^ sm4_rotl32(t, 24);
        end
    endfunction

    function [31:0] sm4_sbox_l;
        input [31:0] x;

        reg [7:0] b0, b1, b2, b3;

        begin
            b0 = sm4_sbox[x[31:24]];
            b1 = sm4_sbox[x[23:16]];
            b2 = sm4_sbox[x[15:8]];
            b3 = sm4_sbox[x[7:0]];
            sm4_sbox_l = {b0, b1, b2, b3};
        end
    endfunction

    function [31:0] sm4_rotl32;
        input [31:0] x;
        input [4:0] n;

        begin
            sm4_rotl32 = {x[31-n], x[31:n]};
        end
    endfunction

    //-------------------------------------------------------------------------
    // Output Assignment
    //-------------------------------------------------------------------------
    assign done = (current_state == SM4_DONE);
    assign output_data = {state_reg, input_data[95:64], input_data[63:32], input_data[31:0]};

endmodule
