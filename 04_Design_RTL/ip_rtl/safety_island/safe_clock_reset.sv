//=============================================================================
// Safe Clock and Reset Monitor
// ASIL-D Safety Critical - Clock/Reset Safety Monitoring
//=============================================================================

`timescale 1ns/1ps

module safe_clock_reset (
    //============================================================================
    // Main Domain Inputs
    //============================================================================
    input  logic                            clk_main_i,
    input  logic                            rst_n_main_i,

    //============================================================================
    // Safety Domain Inputs
    //============================================================================
    input  logic                            clk_safety_i,
    input  logic                            rst_n_safety_i,

    //============================================================================
    // DFT Control
    //============================================================================
    input  logic                            scan_en_i,

    //============================================================================
    // Safety Domain Outputs
    //============================================================================
    output logic                            clk_safety_gated_o,
    output logic                            rst_n_safety_synced_o
);

    //============================================================================
    // Clock Monitor
    //============================================================================
    logic                                   clk_main_safe;
    logic                                   clk_safety_safe;
    logic                                   clk_glitch_detected;
    logic [31:0]                            clk_safety_counter;
    logic [31:0]                            clk_safety_prev;
    logic                                   clk_stable;

    always_ff @(posedge clk_main_i) begin
        clk_safety_prev <= clk_safety_i;
        if (clk_safety_i != clk_safety_prev) begin
            clk_safety_counter <= '0;
        end else begin
            clk_safety_counter <= clk_safety_counter + 1;
        end
    end

    assign clk_stable = (clk_safety_counter > 1000);

    // Clock gating for safety domain
    logic [2:0]                             clk_gating_ff;

    always_latch begin
        if (!clk_main_i) begin
            if (clk_stable && !scan_en_i) begin
                clk_gating_ff[0] = 1'b1;
            end else begin
                clk_gating_ff[0] = 1'b0;
            end
        end
    end

    always_ff @(posedge clk_main_i) begin
        clk_gating_ff[1] <= clk_gating_ff[0];
        clk_gating_ff[2] <= clk_gating_ff[1];
    end

    assign clk_safety_gated_o = clk_gating_ff[2];

    //============================================================================
    // Reset Synchronizer for Safety Domain
    //============================================================================
    logic [2:0]                             rst_sync_chain;

    always_ff @(posedge clk_safety_i or negedge rst_n_main_i) begin
        if (!rst_n_main_i) begin
            rst_sync_chain <= '0;
        end else begin
            rst_sync_chain[0] <= rst_n_safety_i;
            rst_sync_chain[1] <= rst_sync_chain[0];
            rst_sync_chain[2] <= rst_sync_chain[1];
        end
    end

    assign rst_n_safety_synced_o = rst_sync_chain[2];

    //============================================================================
    // Reset Monitor
    //============================================================================
    logic                                   rst_glitch_detected;
    logic                                   rst_debounce_counter [3:0];

    logic [31:0]                            rst_on_counter;
    logic                                   rst_stable;

    always_ff @(posedge clk_main_i or negedge rst_n_main_i) begin
        if (!rst_n_main_i) begin
            rst_on_counter <= '0;
            rst_stable <= 1'b0;
        end else begin
            if (rst_n_safety_i == 1'b0) begin
                if (rst_on_counter < 32'hFFFF) begin
                    rst_on_counter <= rst_on_counter + 1;
                end
            end else begin
                rst_on_counter <= '0;
            end
            rst_stable = (rst_on_counter > 100);
        end
    end

    //============================================================================
    // Safety Error Reporting
    //============================================================================
    logic                                   safety_error;
    logic [31:0]                            safety_error_code;

    always_ff @(posedge clk_main_i or negedge rst_n_main_i) begin
        if (!rst_n_main_i) begin
            safety_error <= 1'b0;
            safety_error_code <= '0;
        end else begin
            if (!clk_stable) begin
                safety_error <= 1'b1;
                safety_error_code <= 32'hC001_0001;
            end else if (!rst_stable) begin
                safety_error <= 1'b1;
                safety_error_code <= 32'hC001_0002;
            end else begin
                safety_error <= 1'b0;
                safety_error_code <= '0;
            end
        end
    end

endmodule
