`timescale 1ns/1ps

module can_bit_timing #
(
    parameter TQ_DIVISOR = 8
)
(
    input  wire                    clk_ref,
    input  wire                    rst_n,
    input  wire [31:0]             btr_config,
    output wire [15:0]             bit_time,
    output wire [5:0]              sync_seg,
    output wire [5:0]              prop_seg,
    output wire [5:0]              phase_seg1,
    output wire [5:0]              phase_seg2
);

    wire [5:0]                     sjw;
    wire [5:0]                     seg1;
    wire [5:0]                     seg2;
    wire [7:0]                     brp;
    wire                           btr_mode;

    assign sjw   = btr_config[11:8];
    assign seg1  = btr_config[15:12];
    assign seg2  = btr_config[19:16];
    assign brp   = btr_config[7:0];
    assign btr_mode = btr_config[20];

    assign sync_seg   = 1;
    assign prop_seg   = seg1[2:0];
    assign phase_seg1 = seg1[5:3] + 1;
    assign phase_seg2 = seg2[2:0];
    assign bit_time   = sync_seg + prop_seg + phase_seg1 + phase_seg2;

    reg  [7:0]                     tq_counter;
    reg                            tq_pulse;
    reg  [5:0]                     bit_counter;
    reg                            bit_pulse;
    reg                            tq_reset;

    always @(posedge clk_ref or negedge rst_n) begin
        if (!rst_n) begin
            tq_counter <= '0;
            tq_reset <= 1'b0;
        end else begin
            if (tq_counter >= brp - 1) begin
                tq_counter <= '0;
                tq_reset <= 1'b1;
            end else begin
                tq_counter <= tq_counter + 1;
                tq_reset <= 1'b0;
            end
        end
    end

    assign tq_pulse = tq_reset;

    always @(posedge clk_ref or negedge rst_n) begin
        if (!rst_n) begin
            bit_counter <= '0;
            bit_pulse <= 1'b0;
        end else begin
            bit_pulse <= 1'b0;
            if (tq_reset) begin
                if (bit_counter >= bit_time - 1) begin
                    bit_counter <= '0;
                    bit_pulse <= 1'b1;
                end else begin
                    bit_counter <= bit_counter + 1;
                end
            end
        end
    end

endmodule
