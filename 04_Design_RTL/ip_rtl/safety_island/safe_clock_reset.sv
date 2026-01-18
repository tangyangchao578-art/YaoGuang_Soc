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
    // RTC Reference Clock (for independent clock monitoring - RTL-CLK-001)
    //============================================================================
    input  logic                            clk_rtc_i,
    input  logic                            rst_n_rtc_i,

    //============================================================================
    // DFT Control
    //============================================================================
    input  logic                            scan_en_i,

    //============================================================================
    // Safety Domain Outputs
    //============================================================================
    output logic                            clk_safety_gated_o,
    output logic                            rst_n_safety_synced_o,

    //============================================================================
    // Clock Monitor Outputs (RTL-CLK-001)
    //============================================================================
    output logic                            clk_main_error_o,
    output logic                            clk_safety_error_o
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
            rst_stable <= (rst_on_counter > 100);  // RTL-CLK-001: Fixed mixed assignment
        end
    end

    //============================================================================
    // Independent Clock Monitor using RTC Reference (RTL-CLK-001)
    //============================================================================
    // This monitor uses the RTC clock as an independent reference to detect
    // clock stop, frequency drift, or anomalies in the main and safety clocks
    logic [31:0]                            clk_main_counter_rtc;
    logic [31:0]                            clk_safety_counter_rtc;
    logic [31:0]                            clk_main_counter_rtc_prev;
    logic [31:0]                            clk_safety_counter_rtc_prev;
    logic                                   clk_main_count_valid;
    logic                                   clk_safety_count_valid;
    logic [31:0]                            rtc_cycle_count;
    logic                                   rtc_cycle_strobe;

    // RTC cycle counter (1ms strobe for monitoring)
    always_ff @(posedge clk_rtc_i or negedge rst_n_rtc_i) begin
        if (!rst_n_rtc_i) begin
            rtc_cycle_count <= '0;
            rtc_cycle_strobe <= 1'b0;
        end else begin
            rtc_cycle_count <= rtc_cycle_count + 1;
            rtc_cycle_strobe <= (rtc_cycle_count == 32'd32767);  // 1ms at 32.768kHz
        end
    end

    // Count main clock cycles between RTC strobes
    always_ff @(posedge clk_main_i or negedge rst_n_main_i) begin
        if (!rst_n_main_i) begin
            clk_main_counter_rtc <= '0;
            clk_main_counter_rtc_prev <= '0;
            clk_main_error_o <= 1'b0;
        end else begin
            if (rtc_cycle_strobe) begin
                // Check if main clock count is within expected range
                // For a 200MHz clock, expect ~200000 counts per RTC ms strobe
                // Allow +/- 10% tolerance: 180000 to 220000
                clk_main_counter_rtc_prev <= clk_main_counter_rtc;
                if ((clk_main_counter_rtc < 32'd180000) || (clk_main_counter_rtc > 32'd220000)) begin
                    clk_main_error_o <= 1'b1;
                end else begin
                    clk_main_error_o <= 1'b0;
                end
                clk_main_counter_rtc <= '0;
            end else begin
                clk_main_counter_rtc <= clk_main_counter_rtc + 1;
            end
        end
    end

    // Count safety clock cycles between RTC strobes
    always_ff @(posedge clk_safety_i or negedge rst_n_main_i) begin
        if (!rst_n_main_i) begin
            clk_safety_counter_rtc <= '0;
            clk_safety_counter_rtc_prev <= '0;
            clk_safety_error_o <= 1'b0;
        end else begin
            if (rtc_cycle_strobe) begin
                // Check if safety clock count is within expected range
                // For a 100MHz safety clock, expect ~100000 counts per RTC ms strobe
                // Allow +/- 10% tolerance: 90000 to 110000
                clk_safety_counter_rtc_prev <= clk_safety_counter_rtc;
                if ((clk_safety_counter_rtc < 32'd90000) || (clk_safety_counter_rtc > 32'd110000)) begin
                    clk_safety_error_o <= 1'b1;
                end else begin
                    clk_safety_error_o <= 1'b0;
                end
                clk_safety_counter_rtc <= '0;
            end else begin
                clk_safety_counter_rtc <= clk_safety_counter_rtc + 1;
            end
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
                safety_error_code <= 32'hC001_0001;  // Safety clock not stable
            end else if (!rst_stable) begin
                safety_error <= 1'b1;
                safety_error_code <= 32'hC001_0002;  // Reset not stable
            end else if (clk_main_error_o) begin
                safety_error <= 1'b1;
                safety_error_code <= 32'hC001_0003;  // Main clock frequency error
            end else if (clk_safety_error_o) begin
                safety_error <= 1'b1;
                safety_error_code <= 32'hC001_0004;  // Safety clock frequency error
            end else begin
                safety_error <= 1'b0;
                safety_error_code <= '0;
            end
        end
    end

endmodule
