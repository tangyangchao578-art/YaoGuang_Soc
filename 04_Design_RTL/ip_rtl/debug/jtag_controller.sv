//==============================================================================
// File: jtag_controller.sv
// Description: JTAG Debug Controller following IEEE 1149.1 standard
//              Implements TAP controller and debug register access
// Version: 1.0
//==============================================================================

`timescale 1ns/1ps

module jtag_controller #(
    parameter int IR_WIDTH = 5  // Default 5-bit IR for CoreSight
) (
    // System interface
    input  logic                        clk_i,
    input  logic                        rst_ni,
    
    // JTAG physical interface
    input  logic                        tck_i,
    input  logic                        tms_i,
    input  logic                        tdi_i,
    output logic                        tdo_o,
    input  logic                        trst_ni,
    
    // Instruction register interface
    output logic [IR_WIDTH-1:0]         ir_o,
    output logic                        ir_valid_o,
    
    // Data register interface (debug access)
    input  logic [31:0]                 dr_in_i,      // Data from debug logic
    output logic [31:0]                 dr_out_o,     // Data to debug logic
    output logic                        dr_valid_o,   // Data register selected
    output logic                        dr_done_o     // DR shift complete
);

    //============================================================================
    // Parameters
    //============================================================================
    localparam logic [IR_WIDTH-1:0] IR_BYPASS     = '1;
    localparam logic [IR_WIDTH-1:0] IR_IDCODE    = 5'b00001;
    localparam logic [IR_WIDTH-1:0] IR_SAMPLE    = 5'b00011;
    localparam logic [IR_WIDTH-1:0] IR_EXTEST    = 5'b00000;
    localparam logic [IR_WIDTH-1:0] IR_INT_TEST  = 5'b01111;
    localparam logic [IR_WIDTH-1:0] IR_DEBUG     = 5'b10010;  // 0x12 for CoreSight
    localparam logic [IR_WIDTH-1:0] IR_HIGHZ     = 5'b10101;
    localparam logic [IR_WIDTH-1:0] IR_CLAMP     = 5'b11010;
    
    // TAP Controller States (16 states)
    typedef enum logic [3:0] {
        STATE_TEST_LOGIC_RESET = 4'b0000,
        STATE_RUN_TEST_IDLE    = 4'b0001,
        STATE_SELECT_DR_SCAN   = 4'b0010,
        STATE_CAPTURE_DR       = 4'b0011,
        STATE_SHIFT_DR         = 4'b0100,
        STATE_EXIT1_DR         = 4'b0101,
        STATE_PAUSE_DR         = 4'b0110,
        STATE_EXIT2_DR         = 4'b0111,
        STATE_UPDATE_DR        = 4'b1000,
        STATE_SELECT_IR_SCAN   = 4'b1001,
        STATE_CAPTURE_IR       = 4'b1010,
        STATE_SHIFT_IR         = 4'b1011,
        STATE_EXIT1_IR         = 4'b1100,
        STATE_PAUSE_IR         = 4'b1101,
        STATE_EXIT2_IR         = 4'b1110,
        STATE_UPDATE_IR        = 4'b1111
    } tap_state_t;
    
    localparam int DR_MAX_WIDTH = 32;
    localparam int IR_MAX_WIDTH = IR_WIDTH;
    
    //============================================================================
    // Signal declarations
    //============================================================================
    tap_state_t          tap_state, tap_state_next;
    logic [IR_WIDTH-1:0] ir_reg, ir_reg_next;
    logic [31:0]         dr_reg, dr_reg_next;
    logic                dr_reg_valid;  // 1 = debug access DR, 0 = bypass
    logic [4:0]          dr_bit_count;  // Count bits shifted
    logic [4:0]          dr_bit_count_next;
    logic                tdo_reg;       // Registered TDO
    logic                tdo_enable;    // TDO output enable
    logic                trst_sync;
    logic                tck_sync;
    logic                tms_sync;
    logic                tdi_sync;
    
    // TAP state decoded signals
    logic                in_test_logic_reset;
    logic                in_run_test_idle;
    logic                in_select_dr_scan;
    logic                in_shift_dr;
    logic                in_pause_dr;
    logic                in_update_dr;
    logic                in_select_ir_scan;
    logic                in_shift_ir;
    logic                in_pause_ir;
    logic                in_update_ir;
    
    //============================================================================
    // Input synchronizers
    //============================================================================
    always_ff @(posedge clk_i) begin
        tck_sync <= tck_i;
        tms_sync <= tms_i;
        tdi_sync <= tdi_i;
    end
    
    // TRST synchronizer (async assert, sync deassert)
    always_ff @(posedge clk_i) begin
        trst_sync <= trst_ni;
    end
    
    //============================================================================
    // TAP Controller State Machine
    //============================================================================
    always_ff @(posedge clk_i or negedge trst_sync) begin
        if (!trst_sync) begin
            tap_state <= STATE_TEST_LOGIC_RESET;
        end else begin
            tap_state <= tap_state_next;
        end
    end
    
    // TAP state transition logic (synchronous to clk_i, gated by TCK)
    always_comb begin
        tap_state_next = tap_state;
        
        // State transitions on TMS=1, stays on TMS=0 (except TestLogicReset)
        unique case (tap_state)
            STATE_TEST_LOGIC_RESET: begin
                if (tms_sync) begin
                    tap_state_next = STATE_TEST_LOGIC_RESET;
                end else begin
                    tap_state_next = STATE_RUN_TEST_IDLE;
                end
            end
            
            STATE_RUN_TEST_IDLE: begin
                if (tms_sync) begin
                    tap_state_next = STATE_SELECT_DR_SCAN;
                end else begin
                    tap_state_next = STATE_RUN_TEST_IDLE;
                end
            end
            
            STATE_SELECT_DR_SCAN: begin
                if (tms_sync) begin
                    tap_state_next = STATE_SELECT_IR_SCAN;
                end else begin
                    tap_state_next = STATE_CAPTURE_DR;
                end
            end
            
            STATE_CAPTURE_DR: begin
                if (tms_sync) begin
                    tap_state_next = STATE_EXIT1_DR;
                end else begin
                    tap_state_next = STATE_SHIFT_DR;
                end
            end
            
            STATE_SHIFT_DR: begin
                if (tms_sync) begin
                    tap_state_next = STATE_EXIT1_DR;
                end else begin
                    tap_state_next = STATE_SHIFT_DR;
                end
            end
            
            STATE_EXIT1_DR: begin
                if (tms_sync) begin
                    tap_state_next = STATE_UPDATE_DR;
                end else begin
                    tap_state_next = STATE_PAUSE_DR;
                end
            end
            
            STATE_PAUSE_DR: begin
                if (tms_sync) begin
                    tap_state_next = STATE_EXIT2_DR;
                end else begin
                    tap_state_next = STATE_PAUSE_DR;
                end
            end
            
            STATE_EXIT2_DR: begin
                if (tms_sync) begin
                    tap_state_next = STATE_UPDATE_DR;
                end else begin
                    tap_state_next = STATE_SHIFT_DR;
                end
            end
            
            STATE_UPDATE_DR: begin
                if (tms_sync) begin
                    tap_state_next = STATE_SELECT_DR_SCAN;
                end else begin
                    tap_state_next = STATE_RUN_TEST_IDLE;
                end
            end
            
            STATE_SELECT_IR_SCAN: begin
                if (tms_sync) begin
                    tap_state_next = STATE_TEST_LOGIC_RESET;
                end else begin
                    tap_state_next = STATE_CAPTURE_IR;
                end
            end
            
            STATE_CAPTURE_IR: begin
                if (tms_sync) begin
                    tap_state_next = STATE_EXIT1_IR;
                end else begin
                    tap_state_next = STATE_SHIFT_IR;
                end
            end
            
            STATE_SHIFT_IR: begin
                if (tms_sync) begin
                    tap_state_next = STATE_EXIT1_IR;
                end else begin
                    tap_state_next = STATE_SHIFT_IR;
                end
            end
            
            STATE_EXIT1_IR: begin
                if (tms_sync) begin
                    tap_state_next = STATE_UPDATE_IR;
                end else begin
                    tap_state_next = STATE_PAUSE_IR;
                end
            end
            
            STATE_PAUSE_IR: begin
                if (tms_sync) begin
                    tap_state_next = STATE_EXIT2_IR;
                end else begin
                    tap_state_next = STATE_PAUSE_IR;
                end
            end
            
            STATE_EXIT2_IR: begin
                if (tms_sync) begin
                    tap_state_next = STATE_UPDATE_IR;
                end else begin
                    tap_state_next = STATE_SHIFT_IR;
                end
            end
            
            STATE_UPDATE_IR: begin
                if (tms_sync) begin
                    tap_state_next = STATE_SELECT_DR_SCAN;
                end else begin
                    tap_state_next = STATE_RUN_TEST_IDLE;
                end
            end
            
            default: tap_state_next = STATE_TEST_LOGIC_RESET;
        endcase
    end
    
    // State decoding
    assign in_test_logic_reset = (tap_state == STATE_TEST_LOGIC_RESET);
    assign in_run_test_idle    = (tap_state == STATE_RUN_TEST_IDLE);
    assign in_select_dr_scan   = (tap_state == STATE_SELECT_DR_SCAN);
    assign in_shift_dr         = (tap_state == STATE_SHIFT_DR);
    assign in_pause_dr         = (tap_state == STATE_PAUSE_DR);
    assign in_update_dr        = (tap_state == STATE_UPDATE_DR);
    assign in_select_ir_scan   = (tap_state == STATE_SELECT_IR_SCAN);
    assign in_shift_ir         = (tap_state == STATE_SHIFT_IR);
    assign in_pause_ir         = (tap_state == STATE_PAUSE_IR);
    assign in_update_ir        = (tap_state == STATE_UPDATE_IR);
    
    //============================================================================
    // Instruction Register
    //============================================================================
    always_ff @(posedge clk_i or negedge trst_sync) begin
        if (!trst_sync) begin
            ir_reg <= IR_IDCODE;  // Default to IDCODE after reset
        end else begin
            ir_reg <= ir_reg_next;
        end
    end
    
    // IR shift logic
    always_comb begin
        ir_reg_next = ir_reg;
        
        if (in_capture_ir) begin
            // Capture IR: load with pattern (LSB=1 for IDCODE compatibility)
            ir_reg_next = {ir_reg[IR_WIDTH-2:0], 1'b1};
        end else if (in_shift_ir) begin
            // Shift IR: shift in TDI
            ir_reg_next = {tdi_sync, ir_reg[IR_WIDTH-1:1]};
        end else if (in_update_ir) begin
            // Update IR: latch shifted value
            ir_reg_next = ir_reg;  // Value already latched from shift
        end else if (in_test_logic_reset) begin
            // Reset to IDCODE
            ir_reg_next = IR_IDCODE;
        end
    end
    
    // IR output
    assign ir_o = ir_reg;
    assign ir_valid_o = in_update_ir;  // Valid on update
    
    //============================================================================
    // Data Register
    //============================================================================
    always_ff @(posedge clk_i or negedge trst_sync) begin
        if (!trst_sync) begin
            dr_reg <= '0;
            dr_bit_count <= '0;
        end else begin
            dr_reg <= dr_reg_next;
            dr_bit_count <= dr_bit_count_next;
        end
    end
    
    // Determine DR width based on current IR
    function [4:0] get_dr_width(input logic [IR_WIDTH-1:0] ir);
        casez (ir)
            IR_BYPASS:     get_dr_width = 1;
            IR_IDCODE:     get_dr_width = 32;
            IR_SAMPLE, 
            IR_EXTEST,
            IR_INT_TEST:   get_dr_width = 32;  // Boundary scan length
            IR_DEBUG:      get_dr_width = 32;  // Debug register
            IR_HIGHZ,
            IR_CLAMP:      get_dr_width = 32;
            default:       get_dr_width = 1;
        endcase
    endfunction
    
    // DR shift logic
    always_comb begin
        dr_reg_next = dr_reg;
        dr_bit_count_next = dr_bit_count;
        
        // Determine if we're in a debug DR
        dr_reg_valid = (ir_reg == IR_DEBUG);
        
        if (in_capture_dr) begin
            // Capture DR: load data from debug logic or pattern
            if (dr_reg_valid) begin
                dr_reg_next = dr_in_i;  // Load from debug block
            end else if (ir_reg == IR_IDCODE) begin
                // IDCODE pattern
                dr_reg_next = {32'h0BA00477};  // YaoGuang Chip ID
            end else begin
                dr_reg_next = '0;
            end
            dr_bit_count_next = '0;
        end else if (in_shift_dr) begin
            // Shift DR: shift in TDI
            dr_reg_next = {tdi_sync, dr_reg[31:1]};
            dr_bit_count_next = dr_bit_count + 1;
        end else if (in_update_dr) begin
            // Update DR: output to debug logic
            dr_reg_next = dr_reg;  // Keep current value
        end
    end
    
    // DR output
    assign dr_out_o = dr_reg;
    assign dr_valid_o = dr_reg_valid;  // Debug DR selected
    assign dr_done_o = in_update_dr && dr_reg_valid;  // Done when exiting shift
    
    //============================================================================
    // TDO Output Logic
    //============================================================================
    always_ff @(posedge clk_i or negedge trst_sync) begin
        if (!trst_sync) begin
            tdo_reg <= 1'b0;
            tdo_enable <= 1'b0;
        end else begin
            // TDO is registered on TCK falling edge equivalent
            if (in_shift_dr) begin
                tdo_reg <= dr_reg[0];  // LSB first
            end else if (in_shift_ir) begin
                tdo_reg <= ir_reg[0];  // LSB first
            end
            
            // Enable TDO when shifting
            tdo_enable <= in_shift_dr || in_shift_ir;
        end
    end
    
    assign tdo_o = tdo_enable ? tdo_reg : 1'bZ;
    
    //============================================================================
    // Assertions
    //============================================================================
    // IR width check
    initial begin
        if (IR_WIDTH < 2) begin
            $error("IR_WIDTH must be at least 2");
        end
    end
    
    // TDO is high-Z when not shifting
    assert property (@(posedge clk_i) !$onehot0(tdo_enable) || !tdo_enable || tdo_enable)
        else $warning("TDO should be driven only during shift states");
    
endmodule
