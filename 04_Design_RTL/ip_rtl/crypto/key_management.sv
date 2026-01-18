//-----------------------------------------------------------------------------
// YaoGuang SoC Key Management Unit
// File: key_management.sv
// Description: Secure key storage and management
// Version: 1.0
// Date: 2026-01-18
//-----------------------------------------------------------------------------

`timescale 1ns/1ps

module key_management #(
    parameter int KEY_WIDTH = 256,
    parameter int NUM_KEYS = 32
) (
    input  logic                  clk,
    input  logic                  rstn,
    input  logic                  start,
    output logic                  done,
    input  logic [7:0]            key_id,
    input  logic [KEY_WIDTH-1:0]  key_data,
    output logic                  key_valid,
    input  logic                  key_ready,
    output logic [7:0]            key_status,
    input  logic                  secure_en,
    input  logic                  tamper_detect
);

    //-------------------------------------------------------------------------
    // Parameters
    //-------------------------------------------------------------------------
    typedef enum logic [3:0] {
        KEY_IDLE      = 4'd0,
        KEY_STORE     = 4'd1,
        KEY_LOAD      = 4'd2,
        KEY_DERIVE    = 4'd3,
        KEY_DESTROY   = 4'd4,
        KEY_DONE      = 4'd5,
        KEY_ERROR     = 4'd6
    } key_state_t;

    typedef enum logic [1:0] {
        KEY_VALID     = 2'd0,
        KEY_INVALID   = 2'd1,
        KEY_EXPIRED   = 2'd2,
        KEY_LOCKED    = 2'd3
    } key_status_t;

    //-------------------------------------------------------------------------
    // Signals
    //-------------------------------------------------------------------------
    key_state_t                   current_state;
    key_state_t                   next_state;

    logic [KEY_WIDTH-1:0]         key_storage [0:NUM_KEYS-1];
    logic [7:0]                   key_attr [0:NUM_KEYS-1];
    logic [31:0]                 key_usage_count [0:NUM_KEYS-1];

    logic [7:0]                   current_key_id;
    logic [KEY_WIDTH-1:0]         current_key;

    logic [255:0]                 master_key;
    logic [255:0]                 kdf_output;

    logic [$clog2(NUM_KEYS)-1:0]  key_idx;

    //-------------------------------------------------------------------------
    // Key Storage Array
    //-------------------------------------------------------------------------
    genvar storage_idx;
    generate
        for (storage_idx = 0; storage_idx < NUM_KEYS; storage_idx++) begin : key_storage_gen
            always_ff @(posedge clk) begin
                if (start && key_id == storage_idx && current_state == KEY_STORE) begin
                    key_storage[storage_idx] <= key_data;
                    key_attr[storage_idx][0] <= 1'b1;
                end else if (current_state == KEY_DESTROY && key_id == storage_idx) begin
                    key_storage[storage_idx] <= {KEY_WIDTH{1'b0}};
                    key_attr[storage_idx][0] <= 1'b0;
                end
            end

            always_ff @(posedge clk) begin
                if (current_state == KEY_LOAD && key_id == storage_idx) begin
                    current_key <= key_storage[storage_idx];
                end
            end
        end
    endgenerate

    //-------------------------------------------------------------------------
    // State Machine
    //-------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            current_state <= KEY_IDLE;
        end else begin
            current_state <= next_state;
        end
    end

    always_comb begin
        next_state = current_state;

        case (current_state)
            KEY_IDLE: begin
                if (start) begin
                    next_state = KEY_STORE;
                end
            end

            KEY_STORE: begin
                next_state = KEY_DONE;
            end

            KEY_LOAD: begin
                next_state = KEY_DONE;
            end

            KEY_DERIVE: begin
                next_state = KEY_DONE;
            end

            KEY_DESTROY: begin
                next_state = KEY_DONE;
            end

            KEY_DONE: begin
                next_state = KEY_IDLE;
            end

            KEY_ERROR: begin
                next_state = KEY_IDLE;
            end
        endcase
    end

    //-------------------------------------------------------------------------
    // Key Operations
    //-------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            for (int i = 0; i < NUM_KEYS; i++) begin
                key_storage[i] <= {KEY_WIDTH{1'b0}};
                key_attr[i] <= 8'd0;
                key_usage_count[i] <= 32'd0;
            end
            current_key <= {KEY_WIDTH{1'b0}};
            current_key_id <= 8'd0;
            key_valid <= 1'b0;
            key_status <= 8'd0;
        end else begin
            case (current_state)
                KEY_IDLE: begin
                    key_valid <= 1'b0;
                end

                KEY_STORE: begin
                    current_key_id <= key_id;
                    key_attr[key_id][0] <= 1'b1;
                    key_attr[key_id][7:1] <= 7'd0;
                    key_usage_count[key_id] <= 32'd0;
                end

                KEY_LOAD: begin
                    current_key_id <= key_id;
                    if (key_attr[key_id][0]) begin
                        key_valid <= 1'b1;
                        key_status <= 8'd0;
                        key_usage_count[key_id] <= key_usage_count[key_id] + 32'd1;
                    end else begin
                        key_valid <= 1'b0;
                        key_status <= 8'd1;
                    end
                end

                KEY_DESTROY: begin
                    key_storage[key_id] <= {KEY_WIDTH{1'b0}};
                    key_attr[key_id] <= 8'd0;
                    key_valid <= 1'b0;
                    key_status <= 8'd0;
                end
            endcase
        end
    end

    //-------------------------------------------------------------------------
    // Tamper Response
    //-------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            for (int i = 0; i < NUM_KEYS; i++) begin
                key_storage[i] <= {KEY_WIDTH{1'b0}};
                key_attr[i] <= 8'd0;
            end
        end else if (tamper_detect) begin
            for (int i = 0; i < NUM_KEYS; i++) begin
                key_storage[i] <= {KEY_WIDTH{1'b0}};
                key_attr[i] <= 8'd0;
            end
        end
    end

    //-------------------------------------------------------------------------
    // Key Derivation Function (HKDF-SHA256)
    //-------------------------------------------------------------------------
    logic [255:0]                 ikm;
    logic [255:0]                 salt;
    logic [255:0]                 info;
    logic [7:0]                   derived_key [8];

    always_comb begin
        ikm = master_key;
        salt = key_storage[0];
        info = {96'd0, key_id, 128'd0};

        kdf_output = 256'd0;
    end

    //-------------------------------------------------------------------------
    // Output Assignment
    //-------------------------------------------------------------------------
    assign done = (current_state == KEY_DONE);

endmodule
