`timescale 1ns/1ps

module gpio_128bit #
(
    parameter WIDTH = 128,
    parameter APB_DW = 32,
    parameter APB_AW = 12
)
(
    input  wire                    clk_apb,
    input  wire                    rst_apb_n,
    input  wire                    clk_gpio,
    input  wire                    rst_gpio_n,

    input  wire [APB_AW-1:0]       paddr,
    input  wire                    pwrite,
    input  wire [APB_DW-1:0]       pwdata,
    input  wire                    psel,
    input  wire                    penable,
    output reg  [APB_DW-1:0]       prdata,
    output reg                     pready,
    output reg                     pslverr,

    input  wire [WIDTH-1:0]        gpio_in,
    output reg  [WIDTH-1:0]        gpio_out,
    output reg  [WIDTH-1:0]        gpio_oe,

    output wire [7:0]              int_raw,

    input  wire                    test_mode,
    input  wire                    scan_enable
);

    localparam REG_DATA_IN   = 'h00;
    localparam REG_DATA_OUT  = 'h04;
    localparam REG_OE        = 'h08;
    localparam REG_INT_EN    = 'h0C;
    localparam REG_INT_POL   = 'h10;
    localparam REG_INT_TYPE  = 'h14;
    localparam REG_INT_STATUS= 'h18;
    localparam REG_INT_CLR   = 'h1C;
    localparam REG_DEBOUNCE  = 'h20;

    localparam WORDS = (WIDTH + 31) / 32;

    wire [31:0]                   gpio_in_word [WORDS-1:0];
    wire [31:0]                   gpio_out_reg [WORDS-1:0];
    wire [31:0]                   gpio_oe_reg [WORDS-1:0];
    wire [31:0]                   int_en_reg [WORDS-1:0];
    wire [31:0]                   int_pol_reg [WORDS-1:0];
    wire [31:0]                   int_type_reg [WORDS-1:0];
    wire [31:0]                   int_status_reg [WORDS-1:0];
    wire [31:0]                   int_clr_reg [WORDS-1:0];
    wire [31:0]                   debounce_reg [WORDS-1:0];

    wire [31:0]                   int_word [WORDS-1:0];

    reg  [31:0]                   prdata_reg;
    reg                            pready_reg;
    reg                            pslverr_reg;

    genvar                         i;
    genvar                         j;

    generate
        for (i = 0; i < WORDS; i = i + 1) begin : WORD
            assign gpio_in_word[i] = gpio_in[i*32+31:i*32];

            always @(posedge clk_apb or negedge rst_apb_n) begin
                if (!rst_apb_n) begin
                    gpio_out_reg[i] <= '0;
                    gpio_oe_reg[i] <= '0;
                    int_en_reg[i] <= '0;
                    int_pol_reg[i] <= '0;
                    int_type_reg[i] <= '0;
                    debounce_reg[i] <= '0;
                end else begin
                    if (psel && penable && pwrite) begin
                        case (paddr[7:0])
                            REG_DATA_OUT: begin
                                gpio_out_reg[i] <= pwdata;
                            end
                            REG_OE: begin
                                gpio_oe_reg[i] <= pwdata;
                            end
                            REG_INT_EN: begin
                                int_en_reg[i] <= pwdata;
                            end
                            REG_INT_POL: begin
                                int_pol_reg[i] <= pwdata;
                            end
                            REG_INT_TYPE: begin
                                int_type_reg[i] <= pwdata;
                            end
                            REG_DEBOUNCE: begin
                                debounce_reg[i] <= pwdata;
                            end
                        endcase
                    end
                end
            end

            always @(posedge clk_apb or negedge rst_apb_n) begin
                if (!rst_apb_n) begin
                    int_status_reg[i] <= '0;
                end else begin
                    if (psel && penable && pwrite && paddr[7:0] == REG_INT_CLR) begin
                        int_status_reg[i] <= int_status_reg[i] & ~pwdata;
                    end else begin
                        int_status_reg[i] <= int_status_reg[i] | int_word[i];
                    end
                end
            end
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
                    REG_DATA_IN: begin
                        prdata_reg <= gpio_in_word[paddr[9:2]];
                    end
                    REG_DATA_OUT: begin
                        prdata_reg <= gpio_out_reg[paddr[9:2]];
                    end
                    REG_OE: begin
                        prdata_reg <= gpio_oe_reg[paddr[9:2]];
                    end
                    REG_INT_EN: begin
                        prdata_reg <= int_en_reg[paddr[9:2]];
                    end
                    REG_INT_POL: begin
                        prdata_reg <= int_pol_reg[paddr[9:2]];
                    end
                    REG_INT_TYPE: begin
                        prdata_reg <= int_type_reg[paddr[9:2]];
                    end
                    REG_INT_STATUS: begin
                        prdata_reg <= int_status_reg[paddr[9:2]];
                    end
                    REG_DEBOUNCE: begin
                        prdata_reg <= debounce_reg[paddr[9:2]];
                    end
                    default: begin
                        prdata_reg <= '0;
                        pslverr_reg <= 1'b1;
                    end
                endcase
            end
        end
    end

    always @(*) begin
        gpio_out = '0;
        gpio_oe = '0;
        for (int i = 0; i < WORDS; i = i + 1) begin
            gpio_out[i*32+31:i*32] = gpio_out_reg[i];
            gpio_oe[i*32+31:i*32] = gpio_oe_reg[i];
        end
    end

    assign prdata = prdata_reg;
    assign pready = pready_reg;
    assign pslverr = pslverr_reg;

    generate
        for (i = 0; i < WORDS; i = i + 1) begin : INT_GEN
            for (j = 0; j < 32; j = j + 1) begin : BIT
                if (i*32+j < WIDTH) begin
                    gpio_int_bit #
                    (
                        .DEBOUNCE_LOG2 (8)
                    ) u_int_bit (
                        .clk           (clk_gpio),
                        .rst_n         (rst_gpio_n),
                        .gpio_in       (gpio_in_word[i][j]),
                        .int_en        (int_en_reg[i][j]),
                        .int_pol       (int_pol_reg[i][j]),
                        .int_type      (int_type_reg[i][j]),
                        .debounce_en   (debounce_reg[i][j]),
                        .int_raw       (int_word[i][j])
                    );
                end
            end
        end
    endgenerate

    assign int_raw = {int_status_reg[0][7:0]};

endmodule

module gpio_int_bit #
(
    parameter DEBOUNCE_LOG2 = 8
)
(
    input  wire                    clk,
    input  wire                    rst_n,
    input  wire                    gpio_in,
    input  wire                    int_en,
    input  wire                    int_pol,
    input  wire                    int_type,
    input  wire                    debounce_en,
    output reg                     int_raw
);

    reg                            sync_in;
    reg                            sync_in_d;
    reg                            debounce_cnt;
    reg  [DEBOUNCE_LOG2-1:0]       debounce_counter;
    reg                            stable_in;
    reg                            edge_detected;
    reg                            level_detected;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sync_in <= 1'b0;
            sync_in_d <= 1'b0;
            stable_in <= 1'b0;
            debounce_counter <= '0;
        end else begin
            sync_in <= gpio_in;
            sync_in_d <= sync_in;

            if (debounce_en) begin
                if (sync_in != stable_in) begin
                    if (debounce_counter == {DEBOUNCE_LOG2{1'b1}}) begin
                        stable_in <= sync_in;
                        debounce_counter <= '0;
                    end else begin
                        debounce_counter <= debounce_counter + 1;
                    end
                end
            end else begin
                stable_in <= sync_in;
            end
        end
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            edge_detected <= 1'b0;
            level_detected <= 1'b0;
            int_raw <= 1'b0;
        end else begin
            if (int_type) begin
                edge_detected <= (stable_in != sync_in_d) && int_en;
                int_raw <= edge_detected;
            end else begin
                level_detected <= (stable_in != int_pol) && int_en;
                int_raw <= level_detected;
            end
        end
    end

endmodule
