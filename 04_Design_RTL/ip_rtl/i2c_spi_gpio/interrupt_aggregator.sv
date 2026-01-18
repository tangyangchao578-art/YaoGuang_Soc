`timescale 1ns/1ps

module interrupt_aggregator #
(
    parameter NUM_SOURCES = 64,
    parameter APB_DW = 32,
    parameter APB_AW = 12
)
(
    input  wire                    clk_apb,
    input  wire                    rst_apb_n,
    input  wire [NUM_SOURCES-1:0]  int_raw,
    input  wire [NUM_SOURCES-1:0]  int_enable,
    output wire [NUM_SOURCES-1:0]  int_raw_out,
    output wire [NUM_SOURCES-1:0]  int_mask_out,
    output wire [NUM_SOURCES-1:0]  int_status,
    output wire                    int_global,

    input  wire [APB_AW-1:0]       paddr,
    input  wire                    pwrite,
    input  wire [APB_DW-1:0]       pwdata,
    input  wire                    psel,
    input  wire                    penable,
    output reg  [APB_DW-1:0]       prdata,
    output reg                     pready,
    output reg                     pslverr
);

    localparam WORDS = (NUM_SOURCES + 31) / 32;
    localparam REG_ENABLE   = 'h00;
    localparam REG_RAW      = 'h04;
    localparam REG_MASKED   = 'h08;
    localparam REG_STATUS   = 'h0C;
    localparam REG_CLR      = 'h10;
    localparam REG_PRIORITY = 'h14;

    wire [31:0]                   enable_reg [WORDS-1:0];
    wire [31:0]                   raw_reg [WORDS-1:0];
    wire [31:0]                   masked_reg [WORDS-1:0];
    wire [31:0]                   status_reg [WORDS-1:0];
    wire [31:0]                   priority_reg [WORDS-1:0];

    wire [31:0]                   clr_reg;

    wire [NUM_SOURCES-1:0]        int_enabled;
    wire [NUM_SOURCES-1:0]        int_masked;
    wire [NUM_SOURCES-1:0]        int_active;
    wire [7:0]                    highest_priority;

    reg  [31:0]                   prdata_reg;
    reg                            pready_reg;
    reg                            pslverr_reg;

    genvar                         i;
    genvar                         j;

    generate
        for (i = 0; i < WORDS; i = i + 1) begin : WORD
            assign enable_reg[i] = int_enable[i*32+31:i*32];
            assign raw_reg[i] = int_raw[i*32+31:i*32];
            assign masked_reg[i] = int_raw[i*32+31:i*32] & enable_reg[i];
            assign int_masked[i*32+31:i*32] = raw_reg[i] & enable_reg[i];

            always @(posedge clk_apb or negedge rst_apb_n) begin
                if (!rst_apb_n) begin
                    status_reg[i] <= '0;
                end else begin
                    if (psel && penable && pwrite && paddr[7:0] == REG_CLR) begin
                        status_reg[i] <= status_reg[i] & ~pwdata;
                    end else begin
                        status_reg[i] <= status_reg[i] | masked_reg[i];
                    end
                end
            end

            assign int_status[i*32+31:i*32] = status_reg[i];
        end
    endgenerate

    always @(posedge clk_apb or negedge rst_apb_n) begin
        if (!rst_apb_n) begin
            prdata_reg <= '0;
            pready_reg <= 1'b0;
            pslverr_reg <= 1'b0;
        end else begin
            pready_reg <= 1'b0;
            pslverr_reg <= 1'b0;

            if (psel && penable) begin
                pready_reg <= 1'b1;
                case (paddr[7:0])
                    REG_ENABLE: begin
                        prdata_reg <= enable_reg[paddr[9:2]];
                    end
                    REG_RAW: begin
                        prdata_reg <= raw_reg[paddr[9:2]];
                    end
                    REG_MASKED: begin
                        prdata_reg <= masked_reg[paddr[9:2]];
                    end
                    REG_STATUS: begin
                        prdata_reg <= status_reg[paddr[9:2]];
                    end
                    default: begin
                        prdata_reg <= '0;
                        pslverr_reg <= 1'b1;
                    end
                endcase
            end
        end
    end

    priority_encoder #
    (
        .NUM_INPUTS (NUM_SOURCES)
    ) u_prio (
        .inputs     (int_masked),
        .priority   (highest_priority),
        .valid      (int_global)
    );

    assign prdata = prdata_reg;
    assign pready = pready_reg;
    assign pslverr = pslverr_reg;
    assign int_raw_out = int_raw;
    assign int_mask_out = int_masked;

endmodule

module priority_encoder #
(
    parameter NUM_INPUTS = 64
)
(
    input  wire [NUM_INPUTS-1:0]   inputs,
    output wire [7:0]              priority,
    output wire                    valid
);

    wire [7:0]                     level_outputs [7:0];
    wire [7:0]                     level_valid [7:0];
    wire [7:0]                     level_priority [7:0];

    generate
        if (NUM_INPUTS <= 8) begin
            assign priority = 8'h00;
            assign valid = |inputs;
        end else if (NUM_INPUTS <= 16) begin
            assign valid = |inputs;
            assign priority = inputs[7:0] ? 8'h00 : {1'b0, inputs[15:8]};
        end else if (NUM_INPUTS <= 32) begin
            assign valid = |inputs;
            assign priority = inputs[7:0] ? 8'h00 :
                             inputs[15:8] ? 8'h08 :
                             inputs[23:16] ? 8'h10 :
                             {1'b0, inputs[31:24]};
        end else begin
            assign valid = |inputs;
            assign priority = inputs[7:0] ? 8'h00 :
                             inputs[15:8] ? 8'h08 :
                             inputs[23:16] ? 8'h10 :
                             inputs[31:24] ? 8'h18 :
                             inputs[39:32] ? 8'h20 :
                             inputs[47:40] ? 8'h28 :
                             inputs[55:48] ? 8'h30 :
                             inputs[63:56] ? 8'h38 : 8'h00;
        end
    endgenerate

endmodule
