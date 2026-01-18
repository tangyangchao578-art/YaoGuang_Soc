//=============================================================================
// Error Reporting Unit
// ASIL-D Safety Critical - Centralized Error Aggregation
//=============================================================================

`timescale 1ns/1ps

module error_reporting_unit (
    //============================================================================
    // Clock and Reset
    //============================================================================
    input  logic                            clk_i,
    input  logic                            rst_n_i,

    //============================================================================
    // Lockstep Error Inputs
    //============================================================================
    input  logic                            lockstep_error_i,
    input  logic [31:0]                     lockstep_error_code_i,

    //============================================================================
    // ECC Error Inputs
    //============================================================================
    input  logic                            ecc_error_i,
    input  logic [31:0]                     ecc_error_code_i,

    //============================================================================
    // Watchdog Error Inputs
    //============================================================================
    input  logic                            watchdog_error_i,
    input  logic                            watchdog_timeout_i,

    //============================================================================
    // Error Outputs
    //============================================================================
    output logic [31:0]                     error_code_o,
    output logic                            error_valid_o,

    //============================================================================
    // Interrupt Outputs
    //============================================================================
    output logic                            irq_lockstep_o,
    output logic                            irq_ecc_o,
    output logic                            irq_watchdog_o
);

    //============================================================================
    // Error Priority Encoding
    //============================================================================
    typedef enum logic [2:0] {
        ERR_NONE       = 3'd0,
        ERR_LOCKSTEP   = 3'd1,
        ERR_ECC        = 3'd2,
        ERR_WATCHDOG   = 3'd3,
        ERR_MULTIPLE   = 3'd4
    } error_type_t;

    error_type_t                            error_priority;

    always_comb begin
        error_priority = ERR_NONE;
        if (lockstep_error_i) begin
            error_priority = ERR_LOCKSTEP;
        end else if (ecc_error_i) begin
            error_priority = ERR_ECC;
        end else if (watchdog_error_i || watchdog_timeout_i) begin
            error_priority = ERR_WATCHDOG;
        end
    end

    //============================================================================
    // Error Code Generation
    //============================================================================
    logic [31:0]                            current_error_code;
    logic [2:0]                             error_source;
    logic [31:0]                            timestamp;

    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            error_code_o <= '0;
            error_valid_o <= 1'b0;
            timestamp <= '0;
        end else begin
            timestamp <= timestamp + 1;

            case (error_priority)
                ERR_LOCKSTEP: begin
                    error_code_o <= lockstep_error_code_i;
                    error_valid_o <= lockstep_error_i;
                    error_source <= 3'd1;
                end
                ERR_ECC: begin
                    error_code_o <= ecc_error_code_i;
                    error_valid_o <= ecc_error_i;
                    error_source <= 3'd2;
                end
                ERR_WATCHDOG: begin
                    error_code_o <= {24'd0, 8'd3};
                    error_valid_o <= watchdog_error_i || watchdog_timeout_i;
                    error_source <= 3'd3;
                end
                default: begin
                    error_code_o <= '0;
                    error_valid_o <= 1'b0;
                    error_source <= '0;
                end
            endcase
        end
    end

    //============================================================================
    // Interrupt Generation
    //============================================================================
    logic [3:0]                             irq_lockstep_pipe;
    logic [3:0]                             irq_ecc_pipe;
    logic [3:0]                             irq_watchdog_pipe;

    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            irq_lockstep_pipe <= '0;
            irq_ecc_pipe <= '0;
            irq_watchdog_pipe <= '0;
            irq_lockstep_o <= 1'b0;
            irq_ecc_o <= 1'b0;
            irq_watchdog_o <= 1'b0;
        end else begin
            irq_lockstep_pipe <= {irq_lockstep_pipe[2:0], lockstep_error_i};
            irq_ecc_pipe <= {irq_ecc_pipe[2:0], ecc_error_i};
            irq_watchdog_pipe <= {irq_watchdog_pipe[2:0], watchdog_error_i || watchdog_timeout_i};

            irq_lockstep_o <= |irq_lockstep_pipe[3:1];
            irq_ecc_o <= |irq_ecc_pipe[3:1];
            irq_watchdog_o <= |irq_watchdog_pipe[3:1];
        end
    end

endmodule
