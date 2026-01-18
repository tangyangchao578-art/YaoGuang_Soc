// Copyright (c) 2026 YaoGuang SoC Project
// All rights reserved

// Module: snoop_control_unit
// Description: Snoop Control Unit for ACE4 Coherency
// Version: 1.0
// Author: Frontend Design Engineer
// Date: 2026-01-19

`timescale 1ns/1ps

module snoop_control_unit (
    //===========================================
    // Clock and Reset
    //===========================================
    input  wire            clk,
    input  wire            rst_n,

    //===========================================
    // ACE4 Snoop Channel Inputs
    //===========================================
    input  wire [3:0]      ace_acsnoop,
    input  wire [4:0]      ace_acdomain,
    input  wire            ace_acparity,

    //===========================================
    // ACE4 Snoop Response Channel Outputs
    //===========================================
    output wire [1:0]      ace_crresp,
    output wire [5:0]      ace_crid,
    output wire            ace_crvalid,
    input  wire            ace_crready,

    //===========================================
    // ACE4 Snoop Data Channel Outputs
    //===========================================
    output wire [511:0]    ace_cddata,
    output wire [63:0]     ace_cdwstrb,
    output wire            ace_cdlast,
    output wire            ace_cdvalid,
    input  wire            ace_cdready,

    //===========================================
    // Core Snoop Interface
    //===========================================
    output wire [7:0]      core_snoop_req,
    input  wire [7:0]      core_snoop_grant,
    input  wire [7:0]      core_snoop_data_valid,
    input  wire [511:0]    core_snoop_data,
    input  wire [63:0]     core_snoop_data_strb,
    input  wire            core_snoop_data_last,
    output wire            core_snoop_resp_ready,

    //===========================================
    // Snoop Filter Interface
    //===========================================
    output wire            snoop_filter_lookup,
    output wire [47:0]     snoop_filter_addr,
    input  wire            snoop_filter_hit,
    input  wire [7:0]      snoop_filter_share_ways,
    input  wire            snoop_filter_dirty,

    //===========================================
    // DVM Interface
    //===========================================
    input  wire            dvm_tlb_invalidate,
    input  wire            dvm_pou_invalidate,
    output wire            dvm_complete,

    //===========================================
    // Status Interface
    //===========================================
    output wire [31:0]     snoop_count,
    output wire [31:0]     dvm_count,
    output wire [7:0]      snoop_fsm_state
);

    //===========================================
    // Parameters
    //===========================================
    localparam FSM_IDLE      = 8'd0;
    localparam FSM_LOOKUP    = 8'd1;
    localparam FSM_REQUEST   = 8'd2;
    localparam FSM_WAIT_RESP = 8'd3;
    localparam FSM_SEND_DATA = 8'd4;
    localparam FSM_COMPLETE  = 8'd5;
    localparam FSM_DVM       = 8'd6;

    // ACE Snoop Types
    localparam SNOOP_READ_NO_SNOOP         = 4'd0;
    localparam SNOOP_READ_ONCE             = 4'd1;
    localparam SNOOP_READ_SHARED           = 4'd2;
    localparam SNOOP_READ_UNIQUE           = 4'd3;
    localparam SNOOP_WRITE_BACK            = 4'd4;
    localparam SNOOP_WRITE_CLEAN           = 4'd5;
    localparam SNOOP_WRITE_INVALID         = 4'd6;
    localparam SNOOP_EVICT                 = 4'd7;
    localparam SNOOP_DVM_MESSAGE           = 4'd8;

    // ACE Response Types
    localparam RESP_OKAY       = 2'd0;
    localparam RESP_EXOKAY     = 2'd1;
    localparam RESP_SLVERR     = 2'd2;
    localparam RESP_DECERR     = 2'd3;

    //===========================================
    // Internal Registers
    //===========================================
    reg [7:0]               fsm_state;
    reg [7:0]               fsm_state_next;

    reg [47:0]              snoop_addr;
    reg [3:0]               snoop_type;
    reg [4:0]               snoop_domain;
    reg [5:0]               snoop_id;
    reg                     snoop_parity;

    reg                     snoop_valid;
    reg [7:0]               snoop_core_mask;
    reg [7:0]               active_core;

    reg [31:0]              snoop_count_reg;
    reg [31:0]              dvm_count_reg;

    //===========================================
    // FSM State Register
    //===========================================
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            fsm_state       <= FSM_IDLE;
        end else begin
            fsm_state       <= fsm_state_next;
        end
    end

    //===========================================
    // FSM Next State Logic
    //===========================================
    always @(*) begin
        case (fsm_state)
            FSM_IDLE: begin
                if (snoop_valid) begin
                    if (snoop_type == SNOOP_DVM_MESSAGE) begin
                        fsm_state_next = FSM_DVM;
                    end else begin
                        fsm_state_next = FSM_LOOKUP;
                    end
                end else begin
                    fsm_state_next = FSM_IDLE;
                end
            end
            FSM_LOOKUP: begin
                fsm_state_next = FSM_REQUEST;
            end
            FSM_REQUEST: begin
                if (core_snoop_grant != 8'd0) begin
                    fsm_state_next = FSM_WAIT_RESP;
                end else begin
                    fsm_state_next = FSM_REQUEST;
                end
            end
            FSM_WAIT_RESP: begin
                if (|core_snoop_data_valid) begin
                    fsm_state_next = FSM_SEND_DATA;
                end else if (snoop_type == SNOOP_READ_NO_SNOOP ||
                            snoop_type == SNOOP_EVICT) begin
                    fsm_state_next = FSM_COMPLETE;
                end else begin
                    fsm_state_next = FSM_WAIT_RESP;
                end
            end
            FSM_SEND_DATA: begin
                if (core_snoop_data_last & ace_cdready) begin
                    fsm_state_next = FSM_COMPLETE;
                end else begin
                    fsm_state_next = FSM_SEND_DATA;
                end
            end
            FSM_COMPLETE: begin
                if (ace_crvalid & ace_crready) begin
                    fsm_state_next = FSM_IDLE;
                end else begin
                    fsm_state_next = FSM_COMPLETE;
                end
            end
            FSM_DVM: begin
                fsm_state_next = FSM_COMPLETE;
            end
            default: fsm_state_next = FSM_IDLE;
        endcase
    end

    //===========================================
    // Snoop Request Latch
    //===========================================
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            snoop_valid     <= 1'b0;
            snoop_addr      <= 48'h0;
            snoop_type      <= 4'd0;
            snoop_domain    <= 5'd0;
            snoop_id        <= 6'd0;
            snoop_parity    <= 1'b0;
        end else begin
            if (fsm_state == FSM_IDLE) begin
                snoop_valid <= 1'b0;
            end else if (ace_acparity & ~snoop_valid) begin
                snoop_valid <= 1'b1;
                snoop_addr  <= {ace_acdomain, 43'h0};
                snoop_type  <= ace_acsnoop;
                snoop_domain<= ace_acdomain;
                snoop_id    <= 6'd0;
                snoop_parity<= ace_acparity;
            end
        end
    end

    //===========================================
    // Snoop Filter Lookup
    //===========================================
    assign snoop_filter_lookup = (fsm_state == FSM_LOOKUP);
    assign snoop_filter_addr   = snoop_addr;

    //===========================================
    // Core Snoop Request
    //===========================================
    assign core_snoop_req = (fsm_state == FSM_REQUEST) ? snoop_core_mask : 8'd0;

    always @(*) begin
        case (snoop_type)
            SNOOP_READ_NO_SNOOP:   snoop_core_mask = 8'd0;
            SNOOP_READ_ONCE:       snoop_core_mask = snoop_filter_hit ? snoop_filter_share_ways : 8'd0;
            SNOOP_READ_SHARED:     snoop_core_mask = snoop_filter_hit ? snoop_filter_share_ways : 8'd0;
            SNOOP_READ_UNIQUE:     snoop_core_mask = snoop_filter_hit ? snoop_filter_share_ways : 8'd0;
            SNOOP_WRITE_BACK:      snoop_core_mask = snoop_filter_hit ? snoop_filter_share_ways : 8'd0;
            SNOOP_WRITE_CLEAN:     snoop_core_mask = snoop_filter_hit ? snoop_filter_share_ways : 8'd0;
            SNOOP_WRITE_INVALID:   snoop_core_mask = snoop_filter_hit ? snoop_filter_share_ways : 8'd0;
            SNOOP_EVICT:           snoop_core_mask = 8'd0;
            SNOOP_DVM_MESSAGE:     snoop_core_mask = 8'd0;
            default:               snoop_core_mask = 8'd0;
        endcase
    end

    //===========================================
    // Response Generation
    //===========================================
    assign ace_crid      = snoop_id;
    assign ace_cdlast    = core_snoop_data_last;
    assign core_snoop_resp_ready = (fsm_state == FSM_WAIT_RESP);

    // Snoop data mux
    reg [511:0] cddata_reg;
    reg [63:0]  cdwstrb_reg;
    reg         cdvalid_reg;

    always @(*) begin
        if (|core_snoop_data_valid) begin
            cddata_reg  = core_snoop_data;
            cdwstrb_reg = core_snoop_data_strb;
            cdvalid_reg = 1'b1;
        end else begin
            cddata_reg  = 512'h0;
            cdwstrb_reg = 64'h0;
            cdvalid_reg = 1'b0;
        end
    end

    assign ace_cddata   = cddata_reg;
    assign ace_cdwstrb  = cdwstrb_reg;
    assign ace_cdvalid  = cdvalid_reg & (fsm_state == FSM_SEND_DATA);

    // Response type based on snoop type
    always @(*) begin
        case (snoop_type)
            SNOOP_READ_NO_SNOOP:   ace_crresp = RESP_OKAY;
            SNOOP_READ_ONCE:       ace_crresp = RESP_OKAY;
            SNOOP_READ_SHARED:     ace_crresp = RESP_OKAY;
            SNOOP_READ_UNIQUE:     ace_crresp = RESP_OKAY;
            SNOOP_WRITE_BACK:      ace_crresp = RESP_OKAY;
            SNOOP_WRITE_CLEAN:     ace_crresp = RESP_OKAY;
            SNOOP_WRITE_INVALID:   ace_crresp = RESP_OKAY;
            SNOOP_EVICT:           ace_crresp = RESP_OKAY;
            SNOOP_DVM_MESSAGE:     ace_crresp = RESP_OKAY;
            default:               ace_crresp = RESP_OKAY;
        endcase
    end

    //===========================================
    // Valid Generation
    //===========================================
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ace_crvalid <= 1'b0;
        end else begin
            if (fsm_state == FSM_COMPLETE) begin
                ace_crvalid <= 1'b1;
            end else if (ace_crready) begin
                ace_crvalid <= 1'b0;
            end
        end
    end

    //===========================================
    // DVM Complete
    //===========================================
    assign dvm_complete = (fsm_state == FSM_DVM);

    //===========================================
    // Counters
    //===========================================
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            snoop_count_reg  <= 32'd0;
            dvm_count_reg    <= 32'd0;
        end else begin
            if (snoop_valid) begin
                if (snoop_type == SNOOP_DVM_MESSAGE) begin
                    dvm_count_reg <= dvm_count_reg + 1;
                end else begin
                    snoop_count_reg <= snoop_count_reg + 1;
                end
            end
        end
    end

    assign snoop_count     = snoop_count_reg;
    assign dvm_count       = dvm_count_reg;
    assign snoop_fsm_state = fsm_state;

endmodule
