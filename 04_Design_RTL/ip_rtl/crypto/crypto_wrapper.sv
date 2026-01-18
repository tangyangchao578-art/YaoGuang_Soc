//-----------------------------------------------------------------------------
// YaoGuang SoC Crypto Wrapper Module
// File: crypto_wrapper.sv
// Description: Security wrapper with access control and isolation
// Version: 1.0
// Date: 2026-01-18
//-----------------------------------------------------------------------------

`timescale 1ns/1ps

module crypto_wrapper #(
    parameter int KEY_WIDTH = 256
) (
    // System Interface
    input  logic              sys_clk,
    input  logic              sys_rstn,
    output logic              crypto_intr,

    // APB Slave Interface (from CPU/PMU)
    input  logic              apb_clk,
    input  logic              presetn,
    input  logic [11:0]       paddr,
    input  logic [31:0]       pwdata,
    output logic [31:0]       prdata,
    input  logic              pwrite,
    input  logic              psel,
    input  logic              penable,
    output logic              pready,
    output logic              pslverr,

    // AXI4-Stream Interface (to/from system)
    input  logic              axis_clk,
    input  logic              axis_rstn,
    input  logic              axis_tvalid_in,
    output logic              axis_tready_out,
    input  logic [127:0]      axis_tdata_in,
    input  logic              axis_tlast_in,
    output logic              axis_tvalid_out,
    input  logic              axis_tready_in,
    output logic [127:0]      axis_tdata_out,
    output logic              axis_tlast_out,

    // Secure Interface (from Safety Island)
    input  logic              secure_clk,
    input  logic              secure_rstn,
    input  logic              secure_access,
    input  logic [11:0]       secure_addr,
    input  logic [31:0]       secure_wdata,
    output logic [31:0]       secure_rdata,
    input  logic              secure_write,
    output logic              secure_ready,
    output logic              secure_error,

    // Key Interface
    output logic              key_write,
    output logic [7:0]        key_id,
    output logic [KEY_WIDTH-1:0] key_data,
    output logic              key_valid,
    input  logic              key_ready,
    input  logic [7:0]        key_status,

    // TRNG Interface
    input  logic              trng_clk,
    input  logic              trng_rstn,
    output logic              trng_en,
    input  logic [31:0]       trng_data,
    input  logic              trng_valid,
    output logic              trng_ready,

    // Power Management
    input  logic              crypto_pwr_on,
    input  logic              crypto_iso,
    output logic              crypto_pwr_ack
);

    //-------------------------------------------------------------------------
    // Parameters
    //-------------------------------------------------------------------------
    typedef enum logic [2:0] {
        PRIV_USER    = 3'd0,
        PRIV_SUPER   = 3'd1,
        PRIV_KERNEL  = 3'd2,
        PRIV_SECURE  = 3'd3
    } privilege_level_t;

    typedef enum logic [3:0] {
        REG_CTRL     = 4'd0,
        REG_STATUS   = 4'd1,
        REG_CONFIG   = 4'd2,
        REG_KEY      = 4'd3,
        REG_TRNG     = 4'd4,
        REG_SECURE   = 4'd5
    } register_bank_t;

    //-------------------------------------------------------------------------
    // Signals
    //-------------------------------------------------------------------------
    crypto_top #(
        .KEY_WIDTH(KEY_WIDTH)
    ) crypto_top_inst (
        .apb_clk(apb_clk),
        .presetn(presetn),
        .paddr(paddr),
        .pwdata(pwdata),
        .prdata(prdata),
        .pwrite(pwrite),
        .psel(psel),
        .penable(penable),
        .pready(pready),
        .pslverr(pslverr),
        .axis_clk(axis_clk),
        .axis_rstn(axis_rstn),
        .axis_tvalid(axis_tvalid_in),
        .axis_tready(axis_tready_out),
        .axis_tdata(axis_tdata_in),
        .axis_tlast(axis_tlast_in),
        .axis_tvalid_out(axis_tvalid_out),
        .axis_tready_in(axis_tready_in),
        .axis_tdata_out(axis_tdata_out),
        .axis_tlast_out(axis_tlast_out),
        .crypto_intr(crypto_intr),
        .crypto_clk(sys_clk),
        .crypto_rstn(sys_rstn),
        .trng_clk(trng_clk),
        .trng_rstn(trng_rstn),
        .trng_en(trng_en),
        .trng_data(trng_data),
        .trng_valid(trng_valid),
        .trng_ready(trng_ready),
        .key_write(key_write),
        .key_id(key_id),
        .key_data(key_data),
        .key_valid(key_valid),
        .key_ready(key_ready),
        .key_status(key_status)
    );

    //-------------------------------------------------------------------------
    // Access Control
    //-------------------------------------------------------------------------
    logic [2:0]                  current_privilege;
    logic [3:0]                  access_region;
    logic                        access_granted;
    logic                        secure_violation;
    logic                        region_locked;

    logic [11:0]                 locked_region;

    always_ff @(posedge apb_clk or negedge presetn) begin
        if (!presetn) begin
            current_privilege <= PRIV_USER;
            region_locked <= 1'b0;
            locked_region <= 12'd0;
        end else begin
            if (psel && penable && pwrite && paddr[11:8] == 4'hF) begin
                case (pwdata[2:0])
                    3'd1: current_privilege <= PRIV_SUPER;
                    3'd2: current_privilege <= PRIV_KERNEL;
                    3'd3: current_privilege <= PRIV_SECURE;
                endcase
            end

            if (psel && penable && pwrite && paddr == 12'hFFC) begin
                region_locked <= pwdata[0];
                locked_region <= pwdata[11:0];
            end
        end
    end

    //-------------------------------------------------------------------------
    // Region Protection
    //-------------------------------------------------------------------------
    always_comb begin
        access_region = paddr[11:8];
        access_granted = 1'b0;
        secure_violation = 1'b0;

        case (access_region)
            4'h0: access_granted = (current_privilege >= PRIV_USER);
            4'h1: access_granted = (current_privilege >= PRIV_SUPER);
            4'h2: access_granted = (current_privilege >= PRIV_KERNEL);
            4'hF: access_granted = (current_privilege == PRIV_SECURE);
            default: secure_violation = 1'b1;
        endcase

        if (region_locked && paddr[11:0] == locked_region) begin
            access_granted = 1'b0;
            secure_violation = 1'b1;
        end
    end

    //-------------------------------------------------------------------------
    // Secure Channel
    //-------------------------------------------------------------------------
    always_ff @(posedge secure_clk or negedge secure_rstn) begin
        if (!secure_rstn) begin
            secure_ready <= 1'b0;
            secure_error <= 1'b0;
            secure_rdata <= 32'd0;
        end else begin
            secure_ready <= 1'b1;
            secure_error <= 1'b0;

            if (secure_access) begin
                if (secure_write) begin
                    secure_ready <= 1'b0;
                end else begin
                    secure_rdata <= prdata;
                end
            end
        end
    end

    //-------------------------------------------------------------------------
    // Power Management
    //-------------------------------------------------------------------------
    logic                        pwr_ctrl_idle;
    logic                        pwr_save_mode;

    always_ff @(posedge sys_clk or negedge sys_rstn) begin
        if (!sys_rstn) begin
            crypto_pwr_ack <= 1'b0;
            pwr_save_mode <= 1'b0;
        end else begin
            crypto_pwr_ack <= crypto_pwr_on;

            if (!crypto_pwr_on) begin
                pwr_save_mode <= 1'b1;
            end else if (crypto_pwr_on && pwr_ctrl_idle) begin
                pwr_save_mode <= 1'b0;
            end
        end
    end

    //-------------------------------------------------------------------------
    // Security Violation Logging
    //-------------------------------------------------------------------------
    logic [31:0]                 violation_count;
    logic [11:0]                 last_violation_addr;
    logic [47:0]                 last_violation_time;
    logic                        violation_logged;

    always_ff @(posedge apb_clk or negedge presetn) begin
        if (!presetn) begin
            violation_count <= 32'd0;
            last_violation_addr <= 12'd0;
            violation_logged <= 1'b0;
        end else begin
            violation_logged <= 1'b0;

            if (secure_violation) begin
                violation_count <= violation_count + 32'd1;
                last_violation_addr <= paddr;
                violation_logged <= 1'b1;
            end
        end
    end

    //-------------------------------------------------------------------------
    // Debug Interface
    //-------------------------------------------------------------------------
    logic                        dbg_enable;
    logic                        dbg_halt;
    logic [31:0]                 dbg_reg_read;
    logic [31:0]                 dbg_reg_write;
    logic [11:0]                 dbg_addr;

    always_ff @(posedge apb_clk or negedge presetn) begin
        if (!presetn) begin
            dbg_enable <= 1'b0;
            dbg_halt <= 1'b0;
        end else begin
            if (psel && penable && pwrite && paddr == 12'hFF8) begin
                dbg_enable <= pwdata[0];
                dbg_halt <= pwdata[1];
            end
        end
    end

endmodule
