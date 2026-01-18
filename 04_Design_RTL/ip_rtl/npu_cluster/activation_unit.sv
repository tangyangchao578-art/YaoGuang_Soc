//-----------------------------------------------------------------------------
// Activation Unit
// File: activation_unit.sv
// Description: Neural Network Activation Function Unit
//              Supports ReLU, PReLU, SiLU, GeLU, Sigmoid, Tanh
//-----------------------------------------------------------------------------
// User: NPU RTL Design Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------

`timescale 1ns/1ps

module activation_unit #
(
    parameter int DATA_WIDTH     = 32,
    parameter int LUT_DEPTH      = 256
)
(
    // Clock and Reset
    input  logic                  clk_i,
    input  logic                  rst_ni,
    input  logic                  enable_i,

    // Activation Type
    // 0000: ReLU, 0001: PReLU, 0010: SiLU, 0011: GeLU
    // 0100: Sigmoid, 0101: Tanh, 0110: Swish, others: Pass-through
    input  logic [3:0]            act_type_i,

    // Input Data
    input  logic [DATA_WIDTH-1:0] data_i,

    // Output Data
    output logic [DATA_WIDTH-1:0] data_o,

    // Control
    output logic                  valid_o
);

    //-------------------------------------------------------------------------
    // Parameters
    //-------------------------------------------------------------------------
    localparam int INT_WIDTH     = 8;
    localparam int FRAC_WIDTH    = 24;

    //-------------------------------------------------------------------------
    // Signals
    //-------------------------------------------------------------------------
    logic [DATA_WIDTH-1:0]        pipe_data [3:0];
    logic                         pipe_valid [3:0];
    logic [3:0]                   pipe_act_type [3:0];

    logic [DATA_WIDTH-1:0]        relu_result;
    logic [DATA_WIDTH-1:0]        prelu_result;
    logic [DATA_WIDTH-1:0]        silu_result;
    logic [DATA_WIDTH-1:0]        gelu_result;
    logic [DATA_WIDTH-1:0]        sigmoid_result;
    logic [DATA_WIDTH-1:0]        tanh_result;
    logic [DATA_WIDTH-1:0]        swish_result;

    logic [7:0]                   alpha_coeff; // PReLU alpha coefficient
    logic                         sign_bit;
    logic [DATA_WIDTH-1:0]        abs_input;
    logic [DATA_WIDTH-1:0]        half_input;

    //-------------------------------------------------------------------------
    // Input Pipeline
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i) begin
        if (enable_i) begin
            pipe_data[0]      <= data_i;
            pipe_valid[0]     <= enable_i;
            pipe_act_type[0]  <= act_type_i;
        end
    end

    //-------------------------------------------------------------------------
    // Pipeline Stages 1-3
    //-------------------------------------------------------------------------
    generate
        for (genvar i = 1; i < 4; i++) begin : GEN_PIPE
            always_ff @(posedge clk_i) begin
                if (enable_i) begin
                    pipe_data[i]      <= pipe_data[i-1];
                    pipe_valid[i]     <= pipe_valid[i-1];
                    pipe_act_type[i]  <= pipe_act_type[i-1];
                end
            end
        end
    endgenerate

    //-------------------------------------------------------------------------
    // ReLU Function
    //-------------------------------------------------------------------------
    assign sign_bit    = pipe_data[2][DATA_WIDTH-1];
    assign abs_input   = sign_bit ? (~pipe_data[2] + 1) : pipe_data[2];

    always_comb begin
        case (pipe_act_type[2])
            4'b0000: begin // ReLU
                relu_result = sign_bit ? 32'b0 : pipe_data[2];
            end
            4'b0001: begin // PReLU
                // Simplified PReLU with fixed alpha = 0.25
                alpha_coeff = 8'd64; // 0.25 in Q8.24 format
                if (sign_bit) begin
                    // negative branch: alpha * x
                    prelu_result = (pipe_data[2] * alpha_coeff) >>> 8;
                end else begin
                    prelu_result = pipe_data[2];
                end
                relu_result = prelu_result;
            end
            4'b0010: begin // SiLU (Swish): x * sigmoid(x)
                relu_result = silu_result;
            end
            4'b0011: begin // GeLU: x * (1 + tanh(sqrt(2/pi) * (x + 0.044715 * x^3)))
                relu_result = gelu_result;
            end
            4'b0100: begin // Sigmoid: 1 / (1 + exp(-x))
                relu_result = sigmoid_result;
            end
            4'b0101: begin // Tanh: (exp(x) - exp(-x)) / (exp(x) + exp(-x))
                relu_result = tanh_result;
            end
            4'b0110: begin // Swish: x * sigmoid(x)
                relu_result = swish_result;
            end
            default: begin // Pass-through
                relu_result = pipe_data[2];
            end
        endcase
    end

    //-------------------------------------------------------------------------
    // SiLU (Swish) Approximation
    //-------------------------------------------------------------------------
    // SiLU approximation: x / (1 + exp(-x))
    assign half_input = pipe_data[2] >>> 1;

    always_ff @(posedge clk_i) begin
        if (enable_i) begin
            // Sigmoid approximation
            logic [31:0] exp_neg_x;
            logic [31:0] sigmoid_val;

            // Simplified sigmoid using piecewise linear approximation
            if (abs_input < 32'd8) begin
                // Sigmoid ~= 0.5 + 0.15 * x for small x
                sigmoid_val = 32'h40000000 + (pipe_data[2] * 32'd4020000) >>> 23;
            end else begin
                // Sigmoid ~= 1 for large positive, 0 for large negative
                sigmoid_val = sign_bit ? 32'b0 : 32'h3F800000;
            end

            // SiLU = x * sigmoid(x)
            silu_result = (pipe_data[2] * sigmoid_val) >>> 16;
        end
    end

    //-------------------------------------------------------------------------
    // GeLU Approximation
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i) begin
        if (enable_i) begin
            // GeLU approximation: x * (1 + tanh(0.8 * x)) / 2
            logic [31:0] tanh_input;
            logic [31:0] tanh_output;

            tanh_input = (pipe_data[2] * 32'd341306030) >>> 24; // 0.8 * x in Q8.24

            // Tanh approximation
            if (tanh_input[31]) begin
                // Negative: tanh(-x) = -tanh(x)
                logic [31:0] abs_tanh;
                abs_tanh = (~tanh_input + 1);
                if (abs_tanh > 32'd16777216) begin // abs(x) > 1
                    tanh_output = 32'hBF800000; // -1
                end else begin
                    // tanh(x) ~= x - x^3/3 for small x
                    tanh_output = abs_tanh - (abs_tanh * abs_tanh * abs_tanh) / 32'd50331648;
                    if (tanh_input[31]) tanh_output = ~tanh_output + 1;
                end
            end else begin
                // Positive
                if (tanh_input > 32'd16777216) begin // x > 1
                    tanh_output = 32'h3F800000; // 1
                end else begin
                    // tanh(x) ~= x - x^3/3
                    tanh_output = tanh_input - (tanh_input * tanh_input * tanh_input) / 32'd50331648;
                end
            end

            // GeLU = x * (1 + tanh) / 2
            gelu_result = (pipe_data[2] * (32'h3F800000 + tanh_output)) >>> 1;
        end
    end

    //-------------------------------------------------------------------------
    // Sigmoid Approximation
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i) begin
        if (enable_i) begin
            // Sigmoid approximation using piecewise linear
            logic [31:0] x_scaled;

            x_scaled = (pipe_data[2] * 32'd16777216) >>> 16; // Scale to Q0.24

            if (x_scaled > 32'd100663296) begin // x > 6
                sigmoid_result = 32'h3F800000; // 1.0
            end else if (x_scaled < 32'd-100663296) begin // x < -6
                sigmoid_result = 32'b0;
            end else begin
                // Sigmoid approximation: 0.5 + 0.218x for -6 < x < 6
                sigmoid_result = 32'h40000000 + (x_scaled * 32'd36909875) >>> 24;
            end
        end
    end

    //-------------------------------------------------------------------------
    // Tanh Approximation
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i) begin
        if (enable_i) begin
            // Tanh approximation using piecewise linear
            if (abs_input > 32'd8388608) begin // |x| > 0.5
                tanh_result = sign_bit ? 32'hBF800000 : 32'h3F800000;
            end else begin
                // tanh(x) ~= x - x^3/3 for small x
                tanh_result = pipe_data[2] - (pipe_data[2] * pipe_data[2] * pipe_data[2]) / 32'd50331648;
            end
        end
    end

    //-------------------------------------------------------------------------
    // Swish (same as SiLU)
    //-------------------------------------------------------------------------
    assign swish_result = silu_result;

    //-------------------------------------------------------------------------
    // Output Pipeline
    //-------------------------------------------------------------------------
    always_ff @(posedge clk_i) begin
        if (enable_i) begin
            data_o  <= relu_result;
            valid_o <= pipe_valid[3];
        end else begin
            valid_o <= 1'b0;
        end
    end

endmodule
