//-----------------------------------------------------------------------------
// YaoGuang SoC AES Engine Module
// File: aes_engine.sv
// Description: AES-128/192/256 encryption/decryption engine
// Version: 1.0
// Date: 2026-01-18
//-----------------------------------------------------------------------------

`timescale 1ns/1ps

module aes_engine #(
    parameter int KEY_WIDTH = 256
) (
    input  logic              clk,
    input  logic              rstn,
    input  logic              start,
    output logic              done,
    input  logic [KEY_WIDTH-1:0] key,
    input  logic [127:0]      iv,
    input  logic [127:0]      input_data,
    output logic [127:0]      output_data,
    input  logic              encrypt,
    input  logic [1:0]        mode,
    input  logic [2:0]        key_len,
    output logic              error
);

    //-------------------------------------------------------------------------
    // Parameters
    //-------------------------------------------------------------------------
    typedef enum logic [3:0] {
        AES_IDLE     = 4'd0,
        AES_KEY_EXP  = 4'd1,
        AES_ROUND_0  = 4'd2,
        AES_ROUND_N  = 4'd3,
        AES_FINAL    = 4'd4,
        AES_DONE     = 4'd5,
        AES_ERROR    = 4'd6
    } aes_state_t;

    typedef enum logic [1:0] {
        MODE_ECB = 2'd0,
        MODE_CBC = 2'd1,
        MODE_CTR = 2'd2,
        MODE_GCM = 2'd3
    } aes_mode_t;

    localparam int NUM_ROUNDS_128 = 10;
    localparam int NUM_ROUNDS_192 = 12;
    localparam int NUM_ROUNDS_256 = 14;

    //-------------------------------------------------------------------------
    // Signals
    //-------------------------------------------------------------------------
    aes_state_t                 current_state;
    aes_state_t                 next_state;

    logic [127:0]               state_reg;
    logic [127:0]               next_state_reg;
    logic [127:0]               round_key [0:14];
    logic [31:0]                round_keys [0:60];

    logic [7:0]                 sbox [0:255];
    logic [7:0]                 inv_sbox [0:255];

    logic [3:0]                 round_num;
    logic [3:0]                 next_round_num;

    logic [127:0]               state_matrix;
    logic [127:0]               temp_state;

    logic [127:0]               ctr_counter;
    logic [127:0]               ghash_state;

    //-------------------------------------------------------------------------
    // S-Box Initialization (ROM)
    //-------------------------------------------------------------------------
    initial begin
        sbox[0]   = 8'h63; sbox[1]   = 8'h7c; sbox[2]   = 8'h77; sbox[3]   = 8'h7b;
        sbox[4]   = 8'hf2; sbox[5]   = 8'h6b; sbox[6]   = 8'h6f; sbox[7]   = 8'hc5;
        sbox[8]   = 8'h30; sbox[9]   = 8'h01; sbox[10]  = 8'h67; sbox[11]  = 8'h2b;
        sbox[12]  = 8'hfe; sbox[13]  = 8'hd7; sbox[14]  = 8'hab; sbox[15]  = 8'h76;
        sbox[16]  = 8'hca; sbox[17]  = 8'h82; sbox[18]  = 8'hc9; sbox[19]  = 8'h7d;
        sbox[20]  = 8'hfa; sbox[21]  = 8'h59; sbox[22]  = 8'h47; sbox[23]  = 8'hf0;
        sbox[24]  = 8'had; sbox[25]  = 8'hd4; sbox[26]  = 8'ha2; sbox[27]  = 8'haf;
        sbox[28]  = 8'h9c; sbox[29]  = 8'ha4; sbox[30]  = 8'h72; sbox[31]  = 8'hc0;
        sbox[32]  = 8'hb7; sbox[33]  = 8'hfd; sbox[34]  = 8'h93; sbox[35]  = 8'h26;
        sbox[36]  = 8'h36; sbox[37]  = 8'h3f; sbox[38]  = 8'hf7; sbox[39]  = 8'hcc;
        sbox[40]  = 8'h34; sbox[41]  = 8'ha5; sbox[42]  = 8'he5; sbox[43]  = 8'hf1;
        sbox[44]  = 8'h71; sbox[45]  = 8'hd8; sbox[46]  = 8'h31; sbox[47]  = 8'h15;
        sbox[48]  = 8'h04; sbox[49]  = 8'hc7; sbox[50]  = 8'h23; sbox[51]  = 8'hc3;
        sbox[52]  = 8'h18; sbox[53]  = 8'h96; sbox[54]  = 8'h05; sbox[55]  = 8'h9a;
        sbox[56]  = 8'h07; sbox[57]  = 8'h12; sbox[58]  = 8'h80; sbox[59]  = 8'he2;
        sbox[60]  = 8'heb; sbox[61]  = 8'h27; sbox[62]  = 8'hb2; sbox[63]  = 8'h75;
        sbox[64]  = 8'h09; sbox[65]  = 8'h83; sbox[66]  = 8'h2c; sbox[67]  = 8'h1a;
        sbox[68]  = 8'h1b; sbox[69]  = 8'h6e; sbox[70]  = 8'h5a; sbox[71]  = 8'ha0;
        sbox[72]  = 8'h52; sbox[73]  = 8'h3b; sbox[74]  = 8'hd6; sbox[75]  = 8'hb3;
        sbox[76]  = 8'h29; sbox[77]  = 8'he3; sbox[78]  = 8'h2f; sbox[79]  = 8'h84;
        sbox[80]  = 8'h53; sbox[81]  = 8'hd1; sbox[82]  = 8'h00; sbox[83]  = 8'hed;
        sbox[84]  = 8'h20; sbox[85]  = 8'hfc; sbox[86]  = 8'hb1; sbox[87]  = 8'h5b;
        sbox[88]  = 8'h6a; sbox[89]  = 8'hcb; sbox[90]  = 8'hbe; sbox[91]  = 8'h39;
        sbox[92]  = 8'h4a; sbox[93]  = 8'h4c; sbox[94]  = 8'h58; sbox[95]  = 8'hcf;
        sbox[96]  = 8'hd0; sbox[97]  = 8'hef; sbox[98]  = 8'haa; sbox[99]  = 8'hfb;
        sbox[100] = 8'h43; sbox[101] = 8'h4d; sbox[102] = 8'h33; sbox[103] = 8'h85;
        sbox[104] = 8'h45; sbox[105] = 8'hf9; sbox[106] = 8'h02; sbox[107] = 8'h7f;
        sbox[108] = 8'h50; sbox[109] = 8'h3c; sbox[110] = 8'h9f; sbox[111] = 8'ha8;
        sbox[112] = 8'h51; sbox[113] = 8'ha3; sbox[114] = 8'h40; sbox[115] = 8'h8f;
        sbox[116] = 8'h92; sbox[117] = 8'h9d; sbox[118] = 8'h38; sbox[119] = 8'hf5;
        sbox[120] = 8'hbc; sbox[121] = 8'hb6; sbox[122] = 8'hda; sbox[123] = 8'h21;
        sbox[124] = 8'h10; sbox[125] = 8'hff; sbox[126] = 8'hf3; sbox[127] = 8'hd2;
        sbox[128] = 8'hcd; sbox[129] = 8'h0c; sbox[130] = 8'h13; sbox[131] = 8'hec;
        sbox[132] = 8'h5f; sbox[133] = 8'h97; sbox[134] = 8'h44; sbox[135] = 8'h17;
        sbox[136] = 8'hc4; sbox[137] = 8'ha7; sbox[138] = 8'h7e; sbox[139] = 8'h3d;
        sbox[140] = 8'h64; sbox[141] = 8'h5d; sbox[142] = 8'h19; sbox[143] = 8'h73;
        sbox[144] = 8'h60; sbox[145] = 8'h81; sbox[146] = 8'h4f; sbox[147] = 8'hdc;
        sbox[148] = 8'h22; sbox[149] = 8'h2a; sbox[150] = 8'h90; sbox[151] = 8'h88;
        sbox[152] = 8'h46; sbox[153] = 8'hee; sbox[154] = 8'hb8; sbox[155] = 8'h14;
        sbox[156] = 8'hde; sbox[157] = 8'h5e; sbox[158] = 8'h0b; sbox[159] = 8'hdb;
        sbox[160] = 8'he0; sbox[161] = 8'h32; sbox[162] = 8'h3a; sbox[163] = 8'h0a;
        sbox[164] = 8'h49; sbox[165] = 8'h06; sbox[166] = 8'h24; sbox[167] = 8'h5c;
        sbox[168] = 8'hc2; sbox[169] = 8'hd3; sbox[170] = 8'hac; sbox[171] = 8'h62;
        sbox[172] = 8'h91; sbox[173] = 8'h95; sbox[174] = 8'h42; sbox[175] = 8'h4f;
        sbox[176] = 8'hbc; sbox[177] = 8'h37; sbox[178] = 8'hc6; sbox[179] = 8'h2e;
        sbox[180] = 8'h08; sbox[181] = 8'h13; sbox[182] = 8'h74; sbox[183] = 8'he4;
        sbox[184] = 8'h7c; sbox[185] = 8'h7d; sbox[186] = 8'h65; sbox[187] = 8'hb9;
        sbox[188] = 8'hf1; sbox[189] = 8'h52; sbox[190] = 8'h6e; sbox[191] = 8'h4b;
        sbox[192] = 8'hfe; sbox[193] = 8'h3b; sbox[194] = 8'h8e; sbox[195] = 8'h44;
        sbox[196] = 8'hc0; sbox[197] = 8'hc9; sbox[198] = 8'h8b; sbox[199] = 8'hd3;
        sbox[200] = 8'h90; sbox[201] = 8'ha8; sbox[202] = 8'h8f; sbox[203] = 8'h8d;
        sbox[204] = 8'h50; sbox[205] = 8'hb8; sbox[206] = 8'h88; sbox[207] = 8'h52;
        sbox[208] = 8'h54; sbox[209] = 8'h24; sbox[210] = 8'h1d; sbox[211] = 8'h20;
        sbox[212] = 8'h61; sbox[213] = 8'h36; sbox[214] = 8'hc5; sbox[215] = 8'hae;
        sbox[216] = 8'he6; sbox[217] = 8'hf4; sbox[218] = 8'h54; sbox[219] = 8'h29;
        sbox[220] = 8'h3b; sbox[221] = 8'ha3; sbox[222] = 8'h1d; sbox[223] = 8'h30;
        sbox[224] = 8'h28; sbox[225] = 8'h46; sbox[226] = 8'h4e; sbox[227] = 8'hb4;
        sbox[228] = 8'hbb; sbox[229] = 8'had; sbox[230] = 8'h2f; sbox[231] = 8'h83;
        sbox[232] = 8'hd9; sbox[233] = 8'h5a; sbox[234] = 8'hd7; sbox[235] = 8'h8e;
        sbox[236] = 8'h5c; sbox[237] = 8'h55; sbox[238] = 8'h4e; sbox[239] = 8'h52;
        sbox[240] = 8'h9e; sbox[241] = 8'h8b; sbox[242] = 8'h4a; sbox[243] = 8'hde;
        sbox[244] = 8'h0e; sbox[245] = 8'h0f; sbox[246] = 8'h5b; sbox[247] = 8'h17;
        sbox[248] = 8'h2b; sbox[249] = 8'h04; sbox[250] = 8'h7e; sbox[251] = 8'hba;
        sbox[252] = 8'h77; sbox[253] = 8'hd6; sbox[254] = 8'h26; sbox[255] = 8'he1;
    end

    //-------------------------------------------------------------------------
    // State Machine
    //-------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            current_state <= AES_IDLE;
        end else begin
            current_state <= next_state;
        end
    end

    always_comb begin
        next_state = current_state;
        error = 1'b0;

        case (current_state)
            AES_IDLE: begin
                if (start) begin
                    next_state = AES_KEY_EXP;
                end
            end

            AES_KEY_EXP: begin
                next_state = AES_ROUND_0;
            end

            AES_ROUND_0: begin
                next_state = AES_ROUND_N;
            end

            AES_ROUND_N: begin
                if (round_num == NUM_ROUNDS_128 - 1 ||
                    (key_len == 3'd1 && round_num == NUM_ROUNDS_192 - 1) ||
                    (key_len == 3'd2 && round_num == NUM_ROUNDS_256 - 1)) begin
                    next_state = AES_FINAL;
                end
            end

            AES_FINAL: begin
                next_state = AES_DONE;
            end

            AES_DONE: begin
                next_state = AES_IDLE;
            end

            AES_ERROR: begin
                error = 1'b1;
                if (start) next_state = AES_KEY_EXP;
            end

            default: next_state = AES_IDLE;
        endcase
    end

    //-------------------------------------------------------------------------
    // Round Counter
    //-------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            round_num <= 4'd0;
        end else begin
            case (current_state)
                AES_ROUND_0: round_num <= 4'd0;
                AES_ROUND_N: round_num <= round_num + 4'd1;
                AES_FINAL:   round_num <= round_num;
            endcase
        end
    end

    //-------------------------------------------------------------------------
    // State Register
    //-------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            state_reg <= 128'd0;
        end else begin
            case (current_state)
                AES_ROUND_0: begin
                    if (encrypt)
                        state_reg <= input_data ^ round_key[0];
                    else
                        state_reg <= input_data;
                end
                AES_ROUND_N, AES_FINAL: begin
                    state_reg <= next_state_reg;
                end
            endcase
        end
    end

    //-------------------------------------------------------------------------
    // Key Expansion
    //-------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            for (int i = 0; i < 15; i++) round_key[i] <= 128'd0;
        end else if (current_state == AES_IDLE && start) begin
            round_key[0] <= key[127:0];
            if (key_len == 3'd0) begin
                for (int i = 1; i < 11; i++) round_key[i] <= aes_key_expand_core(round_key[i-1], i-1, sbox);
            end else if (key_len == 3'd1) begin
                round_key[0] <= key[191:64];
                for (int i = 1; i < 9; i++) round_key[i] <= aes_key_expand_core(round_key[i-1], (i-1)*4, sbox);
                round_key[9] <= key[63:0];
            end else begin
                round_key[0] <= key[255:128];
                for (int i = 1; i < 8; i++) round_key[i] <= aes_key_expand_core(round_key[i-1], (i-1)*4, sbox);
                round_key[8] <= key[127:0];
            end
        end
    end

    function [127:0] aes_key_expand_core;
        input [127:0] prev_key;
        input [7:0] round_num;
        input [7:0] sbox [256];

        reg [31:0] w0, w1, w2, w3;
        reg [31:0] temp;
        reg [7:0] t0, t1, t2, t3;

        begin
            w0 = prev_key[127:96];
            w1 = prev_key[95:64];
            w2 = prev_key[63:32];
            w3 = prev_key[31:0];

            temp = w3;
            t0 = sbox[w3[23:16]];
            t1 = sbox[w3[15:8]];
            t2 = sbox[w3[7:0]];
            t3 = sbox[w3[31:24]] ^ round_num;

            aes_key_expand_core = {t0 ^ w0, t1 ^ w1, t2 ^ w2, t3 ^ w3};
        end
    endfunction

    //-------------------------------------------------------------------------
    // AES Round Functions
    //-------------------------------------------------------------------------
    always_comb begin
        next_state_reg = state_reg;

        case (current_state)
            AES_ROUND_0: begin
                next_state_reg = state_reg;
            end

            AES_ROUND_N: begin
                temp_state = aes_sub_bytes(state_reg, sbox);
                temp_state = aes_shift_rows(temp_state);
                temp_state = aes_mix_columns(temp_state);
                next_state_reg = temp_state ^ round_key[round_num + 1];
            end

            AES_FINAL: begin
                temp_state = aes_sub_bytes(state_reg, sbox);
                temp_state = aes_shift_rows(temp_state);
                next_state_reg = temp_state ^ round_key[round_num + 1];
            end
        endcase
    end

    function [127:0] aes_sub_bytes;
        input [127:0] state_in;
        input [7:0] sbox [256];

        reg [7:0] byte_array [0:15];

        begin
            for (int i = 0; i < 16; i++) begin
                byte_array[i] = sbox[state_in[i*8 +: 8]];
            end
            aes_sub_bytes = {byte_array[0], byte_array[1], byte_array[2], byte_array[3],
                            byte_array[4], byte_array[5], byte_array[6], byte_array[7],
                            byte_array[8], byte_array[9], byte_array[10], byte_array[11],
                            byte_array[12], byte_array[13], byte_array[14], byte_array[15]};
        end
    endfunction

    function [127:0] aes_shift_rows;
        input [127:0] state_in;

        reg [7:0] s0, s1, s2, s3, s4, s5, s6, s7;
        reg [7:0] s8, s9, s10, s11, s12, s13, s14, s15;

        begin
            s0  = state_in[127:120];
            s1  = state_in[95:88];
            s2  = state_in[63:56];
            s3  = state_in[31:24];
            s4  = state_in[119:112];
            s5  = state_in[87:80];
            s6  = state_in[55:48];
            s7  = state_in[23:16];
            s8  = state_in[111:104];
            s9  = state_in[79:72];
            s10 = state_in[47:40];
            s11 = state_in[15:8];
            s12 = state_in[103:96];
            s13 = state_in[71:64];
            s14 = state_in[39:32];
            s15 = state_in[7:0];

            aes_shift_rows = {s0, s5, s10, s15, s4, s9, s14, s3, s8, s13, s2, s12, s1, s6, s11};
        end
    endfunction

    function [127:0] aes_mix_columns;
        input [127:0] state_in;

        reg [31:0] col0, col1, col2, col3;
        reg [31:0] new_col0, new_col1, new_col2, new_col3;

        begin
            col0 = state_in[127:96];
            col1 = state_in[95:64];
            col2 = state_in[63:32];
            col3 = state_in[31:0];

            new_col0 = aes_xtime(col0[23:16]) ^ aes_xtime(col0[15:8]) ^ col0[23:16] ^ col0[15:8] ^ col0[7:0] ^ aes_xtime(col0[31:24]) ^ col0[31:24];
            new_col1 = aes_xtime(col1[31:24]) ^ aes_xtime(col1[23:16]) ^ col1[31:24] ^ col1[23:16] ^ col1[15:8] ^ aes_xtime(col1[7:0]) ^ col1[7:0];
            new_col2 = aes_xtime(col2[23:16]) ^ aes_xtime(col2[15:8]) ^ col2[23:16] ^ col2[15:8] ^ col2[7:0] ^ aes_xtime(col2[31:24]) ^ col2[31:24];
            new_col3 = aes_xtime(col3[31:24]) ^ aes_xtime(col3[23:16]) ^ col3[31:24] ^ col3[23:16] ^ col3[15:8] ^ aes_xtime(col3[7:0]) ^ col3[7:0];

            aes_mix_columns = {new_col0, new_col1, new_col2, new_col3};
        end
    endfunction

    function [7:0] aes_xtime;
        input [7:0] a;

        begin
            if (a[7])
                aes_xtime = {a[6:0], 1'b0} ^ 8'h1b;
            else
                aes_xtime = {a[6:0], 1'b0};
        end
    endfunction

    //-------------------------------------------------------------------------
    // Output Assignment
    //-------------------------------------------------------------------------
    assign done = (current_state == AES_DONE);
    assign output_data = state_reg;

endmodule
