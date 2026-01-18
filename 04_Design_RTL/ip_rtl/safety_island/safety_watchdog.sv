//=============================================================================
// Safety Watchdog Timer
// ASIL-D Safety Critical - Multiple Watchdog Modes
//=============================================================================

`timescale 1ns/1ps

module safety_watchdog (
    //============================================================================
    // Clock and Reset (Independent Safety Clock Domain)
    //============================================================================
    input  logic                            clk_i,
    input  logic                            rst_n_i,
    input  logic                            scan_en_i,

    //============================================================================
    // Watchdog Outputs
    //============================================================================
    output logic                            timeout_o,
    output logic                            error_o,
    output logic                            pulse_o,

    //============================================================================
    // External Watchdog Interface
    //============================================================================
    input  logic                            feedback_i,

    //============================================================================
    // Configuration
    //============================================================================
    input  logic                            cfg_enable_i,

    //============================================================================
    // Error Inputs from Other Safety Modules
    //============================================================================
    input  logic                            lockstep_error_i,
    input  logic                            ecc_error_i,

    //============================================================================
    // Kick Signal (Software Feed)
    //============================================================================
    input  logic                            kick_i
);

    //============================================================================
    // Parameters
    //============================================================================
    parameter int TIMEOUT_MAX = 32'hFFFF_FFFF;

    //============================================================================
    // Registers
    //============================================================================
    logic [31:0]                            counter;
    logic                                   watchdog_enable;
    logic                                   window_mode;
    logic [31:0]                            window_open;
    logic [31:0]                            window_close;
    logic                                   in_window;
    logic                                   early_warning;
    logic                                   pulse_reg;
    logic                                   feedback_sync [2:0];
    logic                                   external_kick;

    //============================================================================
    // Synchronize External Feedback
    //============================================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            feedback_sync[0] <= 1'b0;
            feedback_sync[1] <= 1'b0;
            feedback_sync[2] <= 1'b0;
        end else begin
            feedback_sync[0] <= feedback_i;
            feedback_sync[1] <= feedback_sync[0];
            feedback_sync[2] <= feedback_sync[1];
        end
    end

    assign external_kick = feedback_sync[2];

    //============================================================================
    // Watchdog Enable
    //============================================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            watchdog_enable <= 1'b1;
            window_mode <= 1'b0;
            window_open <= 32'h0000_1000;
            window_close <= 32'h0000_F000;
        end else begin
            watchdog_enable <= cfg_enable_i;
            window_mode <= 1'b1;
            window_open <= 32'h0000_1000;
            window_close <= 32'h0000_F000;
        end
    end

    //============================================================================
    // Window Detection
    //============================================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            in_window <= 1'b0;
        end else begin
            in_window = (counter >= window_open) && (counter < window_close);
        end
    end

    //============================================================================
    // Watchdog Counter
    //============================================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            counter <= '0;
            timeout_o <= 1'b0;
            error_o <= 1'b0;
            early_warning <= 1'b0;
        end else if (!watchdog_enable) begin
            counter <= '0;
            timeout_o <= 1'b0;
            error_o <= 1'b0;
            early_warning <= 1'b0;
        end else begin
            if (kick_i || external_kick) begin
                counter <= '0;
            end else if (counter < TIMEOUT_MAX) begin
                counter <= counter + 1;
            end

            if (counter >= window_close) begin
                timeout_o <= 1'b1;
                error_o <= 1'b1;
            end else if (counter >= (window_close - 32'h0000_0100)) begin
                early_warning <= 1'b1;
            end

            if (lockstep_error_i || ecc_error_i) begin
                error_o <= 1'b1;
            end
        end
    end

    // Pulse Output    //============================================================================
 for External Watchdog
    //============================================================================
    logic [15:0]                            pulse_counter;

    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            pulse_reg <= 1'b0;
            pulse_counter <= '0;
        end else begin
            if (pulse_counter < 100) begin
                pulse_counter <= pulse_counter + 1;
                pulse_reg <= 1'b1;
            end else if (pulse_counter < 200) begin
                pulse_counter <= pulse_counter + 1;
                pulse_reg <= 1'b0;
            end else begin
                pulse_counter <= '0;
            end
        end
    end

    assign pulse_o = pulse_reg && watchdog_enable;

endmodule
