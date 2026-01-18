//-----------------------------------------------------------------------------
// YaoGuang SoC Crypto Top Module
// File: crypto_top.sv
// Description: Top-level crypto accelerator module
// Version: 1.0
// Date: 2026-01-18
//-----------------------------------------------------------------------------

`timescale 1ns/1ps

module crypto_top #(
    parameter int KEY_WIDTH = 256,
    parameter int DATA_WIDTH = 128,
    parameter int NUM_KEYS = 32
) (
    // APB Interface
    input  logic                  apb_clk,
    input  logic                  presetn,
    input  logic [11:0]           paddr,
    input  logic [31:0]           pwdata,
    output logic [31:0]           prdata,
    input  logic                  pwrite,
    input  logic                  psel,
    input  logic                  penable,
    output logic                  pready,
    output logic                  pslverr,

    // AXI4-Stream Data Interface
    input  logic                  axis_clk,
    input  logic                  axis_rstn,
    input  logic                  axis_tvalid,
    output logic                  axis_tready,
    input  logic [DATA_WIDTH-1:0] axis_tdata,
    input  logic                  axis_tlast,
    output logic                  axis_tvalid_out,
    input  logic                  axis_tready_in,
    output logic [DATA_WIDTH-1:0] axis_tdata_out,
    output logic                  axis_tlast_out,

    // Interrupt Interface
    output logic                  crypto_intr,

    // Crypto Engine Clock
    input  logic                  crypto_clk,
    input  logic                  crypto_rstn,

    // TRNG Interface
    input  logic                  trng_clk,
    input  logic                  trng_rstn,
    output logic                  trng_en,
    input  logic [31:0]           trng_data,
    input  logic                  trng_valid,
    output logic                  trng_ready,

    // Key Management Interface
    output logic                  key_write,
    output logic [7:0]            key_id,
    output logic [KEY_WIDTH-1:0]  key_data,
    output logic                  key_valid,
    input  logic                  key_ready,
    input  logic [7:0]            key_status
);

    //-------------------------------------------------------------------------
    // Parameters
    //-------------------------------------------------------------------------
    typedef enum logic [3:0] {
        IDLE          = 4'd0,
        AES_OP        = 4'd1,
        SHA_OP        = 4'd2,
        RSA_OP        = 4'd3,
        ECC_OP        = 4'd4,
        SM2_OP        = 4'd5,
        SM3_OP        = 4'd6,
        SM4_OP        = 4'd7,
        KEY_LOAD      = 4'd8,
        TRNG_READ     = 4'd9,
        DONE          = 4'd10,
        ERROR         = 4'd11
    } crypto_op_t;

    typedef enum logic [1:0] {
        MODE_ECB = 2'd0,
        MODE_CBC = 2'd1,
        MODE_CTR = 2'd2,
        MODE_GCM = 2'd3
    } crypto_mode_t;

    //-------------------------------------------------------------------------
    // Signals
    //-------------------------------------------------------------------------
    logic [31:0]                  reg_ctrl;
    logic [31:0]                  reg_status;
    logic [31:0]                  reg_key_id;
    logic [31:0]                  reg_algo;
    logic [31:0]                  reg_length;
    logic [31:0]                  reg_start;
    logic [31:0]                  reg_intr;
    logic [31:0]                  reg_trng_ctrl;
    logic [31:0]                  reg_key_ctrl;

    logic                         op_start;
    logic                         op_done;
    logic                         op_error;
    logic [3:0]                   current_op;
    logic [3:0]                   next_op;
    crypto_mode_t                 op_mode;

    logic [31:0]                  result_data;
    logic                         result_valid;

    // Engine interface signals
    logic                         aes_start;
    logic                         aes_done;
    logic [127:0]                 aes_key;
    logic [127:0]                 aes_iv;
    logic [127:0]                 aes_input;
    logic [127:0]                 aes_output;
    logic                         aes_encrypt;
    logic                         aes_mode;
    logic [3:0]                   aes_key_len;

    logic                         sha_start;
    logic                         sha_done;
    logic [511:0]                 sha_msg;
    logic                         sha_last;
    logic [255:0]                 sha_digest;

    logic                         trng_start;
    logic                         trng_done;
    logic [255:0]                 trng_entropy;

    logic                         rsa_start;
    logic                         rsa_done;
    logic [4095:0]                rsa_n;
    logic [4095:0]                rsa_d;
    logic [4095:0]                rsa_m;
    logic [4095:0]                rsa_result;

    logic                         ecc_start;
    logic                         ecc_done;
    logic [255:0]                 ecc_k;
    logic [255:0]                 ecc_x;
    logic [255:0]                 ecc_y;
    logic [255:0]                 ecc_result_x;
    logic [255:0]                 ecc_result_y;

    logic                         key_start;
    logic                         key_done;

    logic                         sm4_start;
    logic                         sm4_done;
    logic [127:0]                 sm4_key;
    logic [127:0]                 sm4_iv;
    logic [127:0]                 sm4_input;
    logic [127:0]                 sm4_output;

    // FSM state register
    always_ff @(posedge crypto_clk or negedge crypto_rstn) begin
        if (!crypto_rstn) begin
            current_op <= IDLE;
        end else begin
            current_op <= next_op;
        end
    end

    // FSM next state logic
    always_comb begin
        next_op = current_op;

        case (current_op)
            IDLE: begin
                if (op_start) begin
                    case (reg_algo[3:0])
                        4'd0:   next_op = AES_OP;
                        4'd1:   next_op = SHA_OP;
                        4'd2:   next_op = RSA_OP;
                        4'd3:   next_op = ECC_OP;
                        4'd4:   next_op = SM2_OP;
                        4'd5:   next_op = SM3_OP;
                        4'd6:   next_op = SM4_OP;
                        4'd7:   next_op = KEY_LOAD;
                        4'd8:   next_op = TRNG_READ;
                        default: next_op = ERROR;
                    endcase
                end
            end

            AES_OP: begin
                if (aes_done) next_op = DONE;
                else if (op_error) next_op = ERROR;
            end

            SHA_OP: begin
                if (sha_done) next_op = DONE;
                else if (op_error) next_op = ERROR;
            end

            RSA_OP: begin
                if (rsa_done) next_op = DONE;
                else if (op_error) next_op = ERROR;
            end

            ECC_OP: begin
                if (ecc_done) next_op = DONE;
                else if (op_error) next_op = ERROR;
            end

            SM2_OP: begin
                if (ecc_done) next_op = DONE;
                else if (op_error) next_op = ERROR;
            end

            SM3_OP: begin
                if (sha_done) next_op = DONE;
                else if (op_error) next_op = ERROR;
            end

            SM4_OP: begin
                if (sm4_done) next_op = DONE;
                else if (op_error) next_op = ERROR;
            end

            KEY_LOAD: begin
                if (key_done) next_op = DONE;
            end

            TRNG_READ: begin
                if (trng_done) next_op = DONE;
            end

            DONE: begin
                next_op = IDLE;
            end

            ERROR: begin
                next_op = IDLE;
            end
        endcase
    end

    // APB Slave Interface
    always_ff @(posedge apb_clk or negedge presetn) begin
        if (!presetn) begin
            reg_ctrl      <= 32'd0;
            reg_status    <= 32'd0;
            reg_key_id    <= 32'd0;
            reg_algo      <= 32'd0;
            reg_length    <= 32'd0;
            reg_start     <= 32'd0;
            reg_intr      <= 32'd0;
            reg_trng_ctrl <= 32'd0;
            reg_key_ctrl  <= 32'd0;
            pready        <= 1'b1;
            pslverr       <= 1'b0;
        end else begin
            pready <= 1'b1;

            if (psel && penable && pwrite) begin
                case (paddr[11:0])
                    12'h000: reg_ctrl      <= pwdata;
                    12'h004: reg_status    <= pwdata;
                    12'h008: reg_key_id    <= pwdata;
                    12'h00C: reg_algo      <= pwdata;
                    12'h010: reg_length    <= pwdata;
                    12'h014: reg_start     <= pwdata;
                    12'h018: reg_intr      <= pwdata;
                    12'h01C: reg_trng_ctrl <= pwdata;
                    12'h020: reg_key_ctrl  <= pwdata;
                    default: pslverr <= 1'b1;
                endcase
            end else if (psel && penable && !pwrite) begin
                case (paddr[11:0])
                    12'h000: prdata <= reg_ctrl;
                    12'h004: prdata <= {op_done, op_error, 2'b0, key_status, 1'b0, 2'b0, trng_valid, 2'b0, current_op != IDLE};
                    12'h008: prdata <= reg_key_id;
                    12'h00C: prdata <= reg_algo;
                    12'h010: prdata <= reg_length;
                    12'h014: prdata <= reg_start;
                    12'h018: prdata <= reg_intr;
                    12'h01C: prdata <= reg_trng_ctrl;
                    12'h020: prdata <= reg_key_ctrl;
                    12'h100: prdata <= result_data;
                    default: prdata <= 32'd0;
                endcase
            end
        end
    end

    // Start operation decode
    always_ff @(posedge crypto_clk or negedge crypto_rstn) begin
        if (!crypto_rstn) begin
            op_start <= 1'b0;
        end else begin
            op_start <= reg_start[0];
            if (op_start) reg_start[0] <= 1'b0;
        end
    end

    // Operation done and error
    always_ff @(posedge crypto_clk or negedge crypto_rstn) begin
        if (!crypto_rstn) begin
            op_done  <= 1'b0;
            op_error <= 1'b0;
        end else begin
            case (current_op)
                DONE: begin
                    op_done <= 1'b1;
                    op_error <= 1'b0;
                end
                ERROR: begin
                    op_done <= 1'b1;
                    op_error <= 1'b1;
                end
                default: begin
                    op_done  <= 1'b0;
                    op_error <= 1'b0;
                end
            endcase
        end
    end

    // Interrupt generation
    assign crypto_intr = op_done | op_error;

    //-------------------------------------------------------------------------
    // Sub-module Instantiations
    //-------------------------------------------------------------------------

    // AES Engine
    aes_engine #(
        .KEY_WIDTH(256)
    ) aes_inst (
        .clk           (crypto_clk),
        .rstn          (crypto_rstn),
        .start         (aes_start),
        .done          (aes_done),
        .key           (aes_key),
        .iv            (aes_iv),
        .input_data    (aes_input),
        .output_data   (aes_output),
        .encrypt       (aes_encrypt),
        .mode          (aes_mode),
        .key_len       (aes_key_len),
        .error         (op_error)
    );

    // SHA Engine
    sha_engine sha_inst (
        .clk           (crypto_clk),
        .rstn          (crypto_rstn),
        .start         (sha_start),
        .done          (sha_done),
        .msg           (sha_msg),
        .last          (sha_last),
        .digest        (sha_digest),
        .error         (op_error)
    );

    // TRNG Engine
    trng #(
        .WIDTH(32),
        .FIFO_DEPTH(32)
    ) trng_inst (
        .clk           (trng_clk),
        .rstn          (trng_rstn),
        .enable        (trng_start),
        .done          (trng_done),
        .entropy_out   (trng_entropy),
        .ready         (trng_ready)
    );

    // Key Management
    key_management #(
        .KEY_WIDTH(KEY_WIDTH),
        .NUM_KEYS(NUM_KEYS)
    ) key_mgmt_inst (
        .clk           (crypto_clk),
        .rstn          (crypto_rstn),
        .start         (key_start),
        .done          (key_done),
        .key_id        (reg_key_id[7:0]),
        .key_data      (key_data),
        .key_valid     (key_valid),
        .key_ready     (key_ready),
        .key_status    (key_status)
    );

    // RSA Engine
    rsa_ecc_engine #(
        .KEY_SIZE(2048)
    ) rsa_inst (
        .clk           (crypto_clk),
        .rstn          (crypto_rstn),
        .start         (rsa_start),
        .done          (rsa_done),
        .n             (rsa_n),
        .d             (rsa_d),
        .m             (rsa_m),
        .result        (rsa_result),
        .is_rsa        (1'b1),
        .error         (op_error)
    );

    // ECC Engine
    rsa_ecc_engine #(
        .KEY_SIZE(256)
    ) ecc_inst (
        .clk           (crypto_clk),
        .rstn          (crypto_rstn),
        .start         (ecc_start),
        .done          (ecc_done),
        .n             ({1024{1'b0}}),
        .d             ({1024{1'b0}}),
        .m             ({1024{1'b0}}),
        .result        (),
        .is_rsa        (1'b0),
        .error         (op_error)
    );

    // SM4 Engine
    sm4_engine sm4_inst (
        .clk           (crypto_clk),
        .rstn          (crypto_rstn),
        .start         (sm4_start),
        .done          (sm4_done),
        .key           (sm4_key),
        .iv            (sm4_iv),
        .input_data    (sm4_input),
        .output_data   (sm4_output),
        .mode          (MODE_CBC),
        .error         (op_error)
    );

    // Engine control logic
    always_comb begin
        aes_start = 1'b0;
        sha_start = 1'b0;
        trng_start = 1'b0;
        key_start = 1'b0;
        rsa_start = 1'b0;
        ecc_start = 1'b0;
        sm4_start = 1'b0;

        aes_key = reg_key_id[7:0] * 32;
        aes_iv = 128'd0;
        aes_input = axis_tdata;
        aes_encrypt = reg_algo[4];
        aes_mode = crypto_mode_t'(reg_algo[1:0]);
        aes_key_len = reg_algo[7:5];

        sha_msg = {axis_tdata, 384'd0};
        sha_last = axis_tlast;

        sm4_key = reg_key_id[7:0] * 16;
        sm4_iv = 128'd0;
        sm4_input = axis_tdata;

        case (current_op)
            AES_OP:   aes_start = 1'b1;
            SHA_OP:   sha_start = 1'b1;
            RSA_OP:   rsa_start = 1'b1;
            ECC_OP:   ecc_start = 1'b1;
            SM2_OP:   ecc_start = 1'b1;
            SM3_OP:   sha_start = 1'b1;
            SM4_OP:   sm4_start = 1'b1;
            KEY_LOAD: key_start = 1'b1;
            TRNG_READ: trng_start = 1'b1;
        endcase
    end

    // Result capture
    always_ff @(posedge crypto_clk or negedge crypto_rstn) begin
        if (!crypto_rstn) begin
            result_data <= 32'd0;
            result_valid <= 1'b0;
        end else begin
            result_valid <= 1'b0;
            if (aes_done) begin
                result_data <= aes_output[31:0];
                result_valid <= 1'b1;
            end else if (sha_done) begin
                result_data <= sha_digest[31:0];
                result_valid <= 1'b1;
            end else if (trng_done) begin
                result_data <= trng_entropy[31:0];
                result_valid <= 1'b1;
            end else if (rsa_done) begin
                result_data <= rsa_result[31:0];
                result_valid <= 1'b1;
            end else if (sm4_done) begin
                result_data <= sm4_output[31:0];
                result_valid <= 1'b1;
            end
        end
    end

    // AXI Stream interface
    assign axis_tready = (current_op == AES_OP) | (current_op == SHA_OP) | (current_op == SM4_OP);
    assign axis_tvalid_out = result_valid;
    assign axis_tdata_out = result_valid ? result_data : 128'd0;
    assign axis_tlast_out = result_valid;

    // Key interface
    assign key_id = reg_key_id[7:0];
    assign key_write = key_valid & key_ready;

endmodule
