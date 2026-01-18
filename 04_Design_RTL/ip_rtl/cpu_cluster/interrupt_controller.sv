// Copyright (c) 2026 YaoGuang SoC Project
// All rights reserved

// Module: interrupt_controller
// Description: GIC-600 Compatible Interrupt Controller
// Version: 1.0
// Author: Frontend Design Engineer
// Date: 2026-01-19

`timescale 1ns/1ps

module gic600_controller #(
    parameter NUM_A78AE_IRQS = 32,
    parameter NUM_R52_IRQS   = 64,
    parameter NUM_SPIS       = 32,
    parameter PRI_WIDTH      = 8,
    parameter TARGET_WIDTH   = 8
) (
    //===========================================
    // Clock and Reset
    //===========================================
    input  wire                        clk,
    input  wire                        rst_n,

    //===========================================
    // A78AE Interrupt Interface
    //===========================================
    input  wire [NUM_A78AE_IRQS-1:0]   irq_a78ae_in,
    output wire [NUM_A78AE_IRQS-1:0]   irq_a78ae_out,

    //===========================================
    // R52 Interrupt Interface
    //===========================================
    input  wire [NUM_R52_IRQS-1:0]     irq_r52_in,
    output wire [NUM_R52_IRQS-1:0]     irq_r52_out,

    //===========================================
    // Timer Interrupt Interface
    //===========================================
    output wire [3:0]                  timer_irq_a78ae,
    output wire [1:0]                  timer_irq_r52,

    //===========================================
    // SPI Interface (Software Generated)
    //===========================================
    output wire [TARGET_WIDTH-1:0]     spi_target,
    output wire [10:0]                 spi_id,
    output wire                        spi_valid,
    input  wire                        spi_ready,

    //===========================================
    // APB Configuration Interface
    //===========================================
    input  wire                        apb_psel,
    input  wire                        apb_penable,
    input  wire                        apb_pwrite,
    input  wire [31:0]                 apb_pwdata,
    input  wire [11:0]                 apb_paddr,
    output wire [31:0]                 apb_prdata,
    output wire                        apb_pslverr,

    //===========================================
    // Error Interface
    //===========================================
    output wire [31:0]                 error_out,
    output wire                        error_valid
);

    //===========================================
    // Parameters
    //===========================================
    localparam TOTAL_A78AE_IRQS = NUM_A78AE_IRQS + 4;  // +4 timer IRQs
    localparam TOTAL_R52_IRQS   = NUM_R52_IRQS + 2;    // +2 timer IRQs

    // Register Addresses
    localparam REG_GICD_CTLR      = 12'h000;
    localparam REG_GICD_ISENABLER = 12'h100;
    localparam REG_GICD_ICENABLER = 12'h180;
    localparam REG_GICD_ISPENDR   = 12'h200;
    localparam REG_GICD_ICPENDR   = 12'h280;
    localparam REG_GICD_IPRIORITY = 12'h400;
    localparam REG_GICD_ITARGETSR = 12'h800;
    localparam REG_GICD_ICFGR     = 12'hC00;
    localparam REG_GICD_SGIR      = 12'hF00;

    localparam REG_GICC_CTLR      = 12'h10000;
    localparam REG_GICC_PMR       = 12'h10004;
    localparam REG_GICC_BPR       = 12'h10008;
    localparam REG_GICC_IAR       = 12'h1000C;
    localparam REG_GICC_EOIR      = 12'h10010;

    //===========================================
    // Internal Signals
    //===========================================
    // Distributor Registers
    reg                                 gicd_ctrl_enable;
    reg [31:0]                          gicd_isenable [0:3];
    reg [31:0]                          gicd_ispend [0:3];
    reg [PRI_WIDTH-1:0]                 gicd_priority [0:95];
    reg [TARGET_WIDTH-1:0]              gicd_target [0:95];
    reg [1:0]                           gicd_icfgr [0:23];
    reg [3:0]                           gicd_sgir;

    // CPU Interface Registers
    reg                                 gicc_ctrl_enable;
    reg [PRI_WIDTH-1:0]                 gicc_pmr;
    reg [2:0]                           gicc_bpr;
    reg [10:0]                          gicc_iar;
    reg [10:0]                          gicc_eoir;

    // Interrupt Processing
    wire [7:0]                          highest_pending;
    wire [10:0]                         active_irq;
    wire                                irq_active;
    wire [PRI_WIDTH-1:0]                active_priority;

    // IRQ Status
    wire [NUM_A78AE_IRQS+3:0]           a78ae_irq_status;
    wire [NUM_R52_IRQS+1:0]             r52_irq_status;

    // APB Interface
    reg                                 apb_ready;
    reg [31:0]                          apb_rdata_reg;
    reg                                 apb_err_reg;

    // Counters
    reg [31:0]                          irq_count;
    reg [31:0]                          eoi_count;

    //===========================================
    // IRQ Status Aggregation
    //===========================================
    assign a78ae_irq_status = {timer_irq_a78ae, irq_a78ae_in};
    assign r52_irq_status   = {timer_irq_r52, irq_r52_in};

    //===========================================
    // Priority Encoder (Highest Priority Interrupt)
    //===========================================
    priority_encoder #(
        .WIDTH(96),
        .PRIO_HIGH(1)
    ) u_prio_enc (
        .inputs            ({gicd_isenable[3] & gicd_ispend[3],
                             gicd_isenable[2] & gicd_ispend[2],
                             gicd_isenable[1] & gicd_ispend[1],
                             gicd_isenable[0] & gicd_ispend[0]}),
        .priority          (gicd_priority),
        .valid             (irq_active),
        .irq_id            (active_irq),
        .irq_priority      (active_priority)
    );

    //===========================================
    // Interrupt Output Logic
    //===========================================
    assign irq_a78ae_out = (gicd_isenable[0][NUM_A78AE_IRQS+3:0] &
                           gicd_ispend[0][NUM_A78AE_IRQS+3:0]);

    assign irq_r52_out   = (gicd_isenable[0][NUM_R52_IRQS+1:0] &
                           gicd_ispend[0][NUM_R52_IRQS+1:0]);

    assign timer_irq_a78ae[3:0] = {gicd_isenable[0][NUM_A78AE_IRQS+3:NUM_A78AE_IRQS+0] &
                                   gicd_ispend[0][NUM_A78AE_IRQS+3:NUM_A78AE_IRQS+0]};
    assign timer_irq_r52[1:0]   = {gicd_isenable[0][NUM_R52_IRQS+1:NUM_R52_IRQS+0] &
                                   gicd_ispend[0][NUM_R52_IRQS+1:NUM_R52_IRQS+0]};

    //===========================================
    // SPI Interface
    //===========================================
    assign spi_target    = gicd_target[active_irq[6:0]];
    assign spi_id        = active_irq;
    assign spi_valid     = irq_active & (active_priority < gicc_pmr);
    assign spi_ready     = 1'b1;

    //===========================================
    // APB Write Logic
    //===========================================
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            gicd_ctrl_enable    <= 1'b0;
            gicd_isenable[0]    <= 32'h0;
            gicd_isenable[1]    <= 32'h0;
            gicd_isenable[2]    <= 32'h0;
            gicd_isenable[3]    <= 32'h0;
            gicd_ispend[0]      <= 32'h0;
            gicd_ispend[1]      <= 32'h0;
            gicd_ispend[2]      <= 32'h0;
            gicd_ispend[3]      <= 32'h0;
            gicc_ctrl_enable    <= 1'b0;
            gicc_pmr            <= 8'hFF;
            gicc_bpr            <= 3'd0;
        end else begin
            if (apb_psel & apb_penable & apb_pwrite) begin
                case (apb_paddr)
                    REG_GICD_CTLR: begin
                        gicd_ctrl_enable <= apb_pwdata[0];
                    end
                    REG_GICD_ISENABLER: begin
                        gicd_isenable[0] <= gicd_isenable[0] | apb_pwdata;
                    end
                    REG_GICD_ICENABLER: begin
                        gicd_isenable[0] <= gicd_isenable[0] & ~apb_pwdata;
                    end
                    REG_GICD_ISPENDR: begin
                        gicd_ispend[0] <= gicd_ispend[0] | apb_pwdata;
                    end
                    REG_GICD_ICPENDR: begin
                        gicd_ispend[0] <= gicd_ispend[0] & ~apb_pwdata;
                    end
                    REG_GICD_IPRIORITY: begin
                        gicd_priority[apb_paddr[9:2]] <= apb_pwdata[7:0];
                    end
                    REG_GICD_ITARGETSR: begin
                        gicd_target[apb_paddr[9:2]] <= apb_pwdata[7:0];
                    end
                    REG_GICD_ICFGR: begin
                        gicd_icfgr[apb_paddr[7:2]] <= apb_pwdata[1:0];
                    end
                    REG_GICC_CTLR: begin
                        gicc_ctrl_enable <= apb_pwdata[0];
                    end
                    REG_GICC_PMR: begin
                        gicc_pmr <= apb_pwdata[7:0];
                    end
                    REG_GICC_BPR: begin
                        gicc_bpr <= apb_pwdata[2:0];
                    end
                endcase
            end
        end
    end

    //===========================================
    // APB Read Logic
    //===========================================
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            apb_rdata_reg <= 32'h0;
            apb_err_reg   <= 1'b0;
        end else begin
            apb_err_reg   <= 1'b0;
            case (apb_paddr)
                REG_GICD_CTLR:    apb_rdata_reg <= {31'h0, gicd_ctrl_enable};
                REG_GICD_ISENABLER: apb_rdata_reg <= gicd_isenable[0];
                REG_GICD_ICENABLER: apb_rdata_reg <= ~gicd_isenable[0];
                REG_GICD_ISPENDR:  apb_rdata_reg <= gicd_ispend[0];
                REG_GICD_ICPENDR:  apb_rdata_reg <= ~gicd_ispend[0];
                REG_GICD_IPRIORITY: apb_rdata_reg <= {24'h0, gicd_priority[apb_paddr[9:2]]};
                REG_GICD_ITARGETSR: apb_rdata_reg <= {24'h0, gicd_target[apb_paddr[9:2]]};
                REG_GICD_ICFGR:    apb_rdata_reg <= {30'h0, gicd_icfgr[apb_paddr[7:2]]};
                REG_GICD_SGIR:     apb_rdata_reg <= 32'h0;
                REG_GICC_CTLR:     apb_rdata_reg <= {31'h0, gicc_ctrl_enable};
                REG_GICC_PMR:      apb_rdata_reg <= {24'h0, gicc_pmr};
                REG_GICC_BPR:      apb_rdata_reg <= {29'h0, gicc_bpr};
                REG_GICC_IAR:      apb_rdata_reg <= {21'h0, gicc_iar};
                REG_GICC_EOIR:     apb_rdata_reg <= 32'h0;
                default:           apb_rdata_reg <= 32'h0;
            endcase
        end
    end

    //===========================================
    // IRQ Input Processing (Edge/Level Sensitive)
    //===========================================
    genvar i;
    generate
        for (i = 0; i < NUM_A78AE_IRQS; i = i + 1) begin : A78AE_IRQ_GEN
            always @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    gicd_ispend[0][i] <= 1'b0;
                end else begin
                    if (irq_a78ae_in[i] & gicd_isenable[0][i]) begin
                        gicd_ispend[0][i] <= 1'b1;
                    end else if (gicd_ispend[0][i] & gicd_icfgr[0][1]) begin
                        if (gicc_eoir == i) begin
                            gicd_ispend[0][i] <= 1'b0;
                        end
                    end else if (gicd_ispend[0][i] & ~gicd_icfgr[0][1]) begin
                        gicd_ispend[0][i] <= irq_a78ae_in[i];
                    end
                end
            end
        end

        for (i = 0; i < NUM_R52_IRQS; i = i + 1) begin : R52_IRQ_GEN
            always @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    gicd_ispend[0][NUM_A78AE_IRQS+4+i] <= 1'b0;
                end else begin
                    if (irq_r52_in[i] & gicd_isenable[0][NUM_A78AE_IRQS+4+i]) begin
                        gicd_ispend[0][NUM_A78AE_IRQS+4+i] <= 1'b1;
                    end else if (gicd_ispend[0][NUM_A78AE_IRQS+4+i]) begin
                        if (gicc_eoir == (NUM_A78AE_IRQS+4+i)) begin
                            gicd_ispend[0][NUM_A78AE_IRQS+4+i] <= 1'b0;
                        end
                    end
                end
            end
        end
    endgenerate

    //===========================================
    // Interrupt Acknowledge / EOI
    //===========================================
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            gicc_iar <= 11'd0;
        end else begin
            if (irq_active & (active_priority < gicc_pmr)) begin
                gicc_iar <= active_irq;
                irq_count <= irq_count + 1;
            end
        end
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            gicc_eoir <= 11'd0;
        end else begin
            if (apb_psel & apb_penable & apb_pwrite &
                (apb_paddr == REG_GICC_EOIR)) begin
                gicc_eoir <= apb_pwdata[10:0];
                eoi_count <= eoi_count + 1;
            end
        end
    end

    //===========================================
    // APB Outputs
    //===========================================
    assign apb_prdata   = apb_rdata_reg;
    assign apb_pslverr  = apb_err_reg;

    //===========================================
    // Error Interface
    //===========================================
    assign error_out    = 32'h0;
    assign error_valid  = 1'b0;

endmodule

//===========================================
// Priority Encoder
//===========================================
module priority_encoder #(
    parameter WIDTH = 96,
    parameter PRIO_HIGH = 1
) (
    input  wire [WIDTH-1:0]           inputs,
    input  wire [WIDTH*8-1:0]         priority,
    output wire                       valid,
    output wire [10:0]                irq_id,
    output wire [7:0]                 irq_priority
);

    wire [WIDTH-1:0] masked_inputs = inputs;
    integer i;
    reg [WIDTH-1:0] temp;
    reg [6:0] highest_index;
    reg found;

    always @(*) begin
        highest_index = 0;
        found = 1'b0;
        for (i = WIDTH-1; i >= 0; i = i - 1) begin
            if (!found && masked_inputs[i]) begin
                highest_index = i[6:0];
                found = 1'b1;
            end
        end
    end

    assign valid         = |masked_inputs;
    assign irq_id        = {4'd0, highest_index};
    assign irq_priority  = priority[highest_index*8 +: 8];

endmodule

endmodule
