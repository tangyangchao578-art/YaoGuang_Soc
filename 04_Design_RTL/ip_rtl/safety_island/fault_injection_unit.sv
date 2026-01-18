//=============================================================================
// Fault Injection Unit
// ASIL-D Safety Critical - For BIST and Self-Test
//=============================================================================

`timescale 1ns/1ps

module fault_injection_unit (
    //============================================================================
    // Clock and Reset
    //============================================================================
    input  logic                            clk_i,
    input  logic                            rst_n_i,
    input  logic                            scan_en_i,

    //============================================================================
    // Error Inputs from Safety Monitors
    //============================================================================
    input  logic                            lockstep_error_i,
    input  logic                            ecc_error_i,
    input  logic                            watchdog_error_i,

    //============================================================================
    // SRAM Interface
    //============================================================================
    output logic [31:0]                     sram_addr_o,
    output logic [63:0]                     sram_wdata_o,
    input  logic [63:0]                     sram_rdata_i,
    output logic                            sram_we_o,
    output logic [7:0]                      sram_wstrb_o,

    //============================================================================
    // BIST Configuration
    //============================================================================
    input  logic                            enable_i,
    output logic                            bist_done_o
);

    //============================================================================
    // Parameters
    //============================================================================
    parameter int DATA_WIDTH = 64;
    parameter int ADDR_WIDTH = 32;

    //============================================================================
    // Registers
    //============================================================================
    logic [7:0]                             fault_type;
    logic [31:0]                            fault_addr;
    logic [7:0]                             fault_mask;
    logic                                   inject_enable;
    logic [7:0]                             test_count;
    logic                                   test_complete;
    logic [63:0]                            original_data;
    logic [63:0]                            corrupted_data;

    //============================================================================
    // Fault Injection State Machine
    //============================================================================
    typedef enum logic [2:0] {
        IDLE        = 3'd0,
        READ        = 3'd1,
        CORRUPT     = 3'd2,
        WRITE       = 3'd3,
        VERIFY      = 3'd4,
        RESTORE     = 3'd5,
        DONE        = 3'd6
    } fault_state_t;

    fault_state_t                           state, state_next;

    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            state <= IDLE;
            test_count <= '0;
        end else begin
            state <= state_next;
            if (state == READ || state == CORRUPT || state == WRITE) begin
                test_count <= test_count + 1;
            end
        end
    end

    always_comb begin
        state_next = state;
        case (state)
            IDLE: begin
                if (enable_i) begin
                    state_next = READ;
                end
            end
            READ: begin
                state_next = CORRUPT;
            end
            CORRUPT: begin
                state_next = WRITE;
            end
            WRITE: begin
                state_next = VERIFY;
            end
            VERIFY: begin
                if (test_count < 100) begin
                    state_next = READ;
                end else begin
                    state_next = RESTORE;
                end
            end
            RESTORE: begin
                state_next = DONE;
            end
            DONE: begin
                if (!enable_i) begin
                    state_next = IDLE;
                end
            end
        endcase
    end

    //============================================================================
    // Fault Injection Logic
    //============================================================================
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            fault_type <= '0;
            fault_addr <= '0;
            fault_mask <= '0;
            inject_enable <= 1'b0;
            original_data <= '0;
            corrupted_data <= '0;
        end else begin
            fault_type <= test_count[2:0];
            fault_addr <= {24'd0, test_count[7:0]};
            fault_mask <= {8{test_count[0]}};

            case (fault_type)
                3'd0: corrupted_data = original_data & ~fault_mask;
                3'd1: corrupted_data = original_data | fault_mask;
                3'd2: corrupted_data = original_data ^ fault_mask;
                3'd3: corrupted_data = {original_data[0], original_data[63:1]};
                default: corrupted_data = original_data;
            endcase
        end
    end

    //============================================================================
    // SRAM Control
    //============================================================================
    assign sram_addr_o  = fault_addr;
    assign sram_wdata_o = (state == WRITE) ? corrupted_data : original_data;
    assign sram_we_o    = (state == WRITE || state == RESTORE);
    assign sram_wstrb_o = (state == WRITE || state == RESTORE) ? 8'hFF : 8'd0;

    always_ff @(posedge clk_i) begin
        if (state == READ) begin
            original_data <= sram_rdata_i;
        end
    end

    //============================================================================
    // BIST Done Signal
    //============================================================================
    assign bist_done_o = (state == DONE);

endmodule
