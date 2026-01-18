//-----------------------------------------------------------------------------
// Power State Machine - Main Power Management FSM
//-----------------------------------------------------------------------------

`timescale 1ns/1ps

module power_state_machine (
    input  wire         clk,
    input  wire         rstn,
    input  wire [3:0]   target_state,   // Target power state
    input  wire [9:0]   pd_enable,      // Power domain enable
    output wire [9:0]   pd_iso_n,       // Power domain isolation
    output wire [9:0]   pd_ret_n,       // Power domain retention
    output wire [3:0]   power_state,    // Current power state
    output wire         busy,
    output wire         error
);

    // Local Parameters
    localparam NUM_PD = 10;

    // Power State Definition
    localparam ST_POWER_OFF    = 4'd0;
    localparam ST_POWER_ON     = 4'd1;
    localparam ST_INIT         = 4'd2;
    localparam ST_ACTIVE       = 4'd3;
    localparam ST_IDLE         = 4'd4;
    localparam ST_STANDBY      = 4'd5;
    localparam ST_SLEEP        = 4'd6;
    localparam ST_DEEP_SLEEP   = 4'd7;
    localparam ST_SHUTDOWN     = 4'd8;
    localparam ST_FAULT        = 4'd15;

    // Power Domain Configuration per State
    localparam [9:0] PD_ACTIVE     = 10'b1111111111;  // All on
    localparam [9:0] PD_IDLE       = 10'b1111111111;  // All on
    localparam [9:0] PD_STANDBY    = 10'b1111111110;  // Except RTC
    localparam [9:0] PD_SLEEP      = 10'b1111110000;  // CPU/NPU/GPU off
    localparam [9:0] PD_DEEP_SLEEP = 10'b1111000000;  // Only NOC/MEM/SYS
    localparam [9:0] PD_SHUTDOWN   = 10'b1000000000;  // Only RTC

    // Timing Parameters (in us)
    localparam T_POWER_ON     = 100;
    localparam T_POWER_OFF    = 50;
    localparam T_INIT         = 200;
    localparam T_RETENTION    = 50;
    localparam T_STATE_CHANGE = 20;

    // Registers
    reg  [3:0]   cur_state;
    reg  [3:0]   nxt_state;
    reg  [9:0]   pd_enable_reg;
    reg  [9:0]   pd_iso_n_reg;
    reg  [9:0]   pd_ret_n_reg;
    reg  [31:0]  timer;
    reg          error_reg;

    // State Machine
    always @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            cur_state    <= ST_POWER_OFF;
            pd_enable_reg <= '0;
            pd_iso_n_reg  <= '1;
            pd_ret_n_reg  <= '1;
            timer         <= '0;
            error_reg     <= 1'b0;
        end else begin
            cur_state <= nxt_state;
            case (nxt_state)
                ST_POWER_OFF: begin
                    pd_enable_reg <= '0;
                    pd_iso_n_reg  <= '1;
                    pd_ret_n_reg  <= '1;
                end
                ST_POWER_ON: begin
                    pd_enable_reg <= PD_ACTIVE;
                    timer <= '0;
                end
                ST_INIT: begin
                    timer <= timer + 1;
                    if (timer >= T_INIT) begin
                        pd_iso_n_reg <= '0;
                    end
                end
                ST_ACTIVE: begin
                    pd_enable_reg <= PD_ACTIVE;
                    pd_iso_n_reg  <= '0;
                    pd_ret_n_reg  <= '1;
                end
                ST_IDLE: begin
                    pd_enable_reg <= PD_IDLE;
                    pd_iso_n_reg  <= '0;
                    pd_ret_n_reg  <= '1;
                end
                ST_STANDBY: begin
                    pd_enable_reg <= PD_STANDBY;
                    pd_iso_n_reg  <= '0;
                    pd_ret_n_reg  <= '0;
                end
                ST_SLEEP: begin
                    pd_enable_reg <= PD_SLEEP;
                    timer <= '0;
                end
                ST_DEEP_SLEEP: begin
                    pd_enable_reg <= PD_DEEP_SLEEP;
                    timer <= '0;
                end
                ST_SHUTDOWN: begin
                    pd_enable_reg <= PD_SHUTDOWN;
                    pd_iso_n_reg  <= '1;
                    pd_ret_n_reg  <= '0;
                end
                ST_FAULT: begin
                    pd_enable_reg <= PD_SHUTDOWN;
                    error_reg     <= 1'b1;
                end
            endcase
        end
    end

    // Next State Logic
    always @(*) begin
        nxt_state = cur_state;
        case (cur_state)
            ST_POWER_OFF: begin
                if (target_state == ST_POWER_ON || target_state == ST_INIT)
                    nxt_state = ST_POWER_ON;
            end
            ST_POWER_ON: begin
                if (timer >= T_POWER_ON)
                    nxt_state = ST_INIT;
            end
            ST_INIT: begin
                if (timer >= T_INIT)
                    nxt_state = ST_ACTIVE;
            end
            ST_ACTIVE: begin
                case (target_state)
                    ST_IDLE:        nxt_state = ST_IDLE;
                    ST_STANDBY:     nxt_state = ST_STANDBY;
                    ST_SLEEP:       nxt_state = ST_SLEEP;
                    ST_DEEP_SLEEP:  nxt_state = ST_DEEP_SLEEP;
                    ST_SHUTDOWN:    nxt_state = ST_SHUTDOWN;
                    default:        nxt_state = ST_ACTIVE;
                endcase
            end
            ST_IDLE: begin
                case (target_state)
                    ST_ACTIVE:      nxt_state = ST_ACTIVE;
                    ST_STANDBY:     nxt_state = ST_STANDBY;
                    ST_SLEEP:       nxt_state = ST_SLEEP;
                    default:        nxt_state = ST_IDLE;
                endcase
            end
            ST_STANDBY: begin
                case (target_state)
                    ST_ACTIVE:      nxt_state = ST_ACTIVE;
                    ST_IDLE:        nxt_state = ST_IDLE;
                    ST_SLEEP:       nxt_state = ST_SLEEP;
                    default:        nxt_state = ST_STANDBY;
                endcase
            end
            ST_SLEEP: begin
                case (target_state)
                    ST_ACTIVE:      nxt_state = ST_ACTIVE;
                    ST_DEEP_SLEEP:  nxt_state = ST_DEEP_SLEEP;
                    default:        nxt_state = ST_SLEEP;
                endcase
            end
            ST_DEEP_SLEEP: begin
                case (target_state)
                    ST_ACTIVE:      nxt_state = ST_ACTIVE;
                    default:        nxt_state = ST_DEEP_SLEEP;
                endcase
            end
            ST_SHUTDOWN: begin
                case (target_state)
                    ST_POWER_ON:    nxt_state = ST_POWER_ON;
                    default:        nxt_state = ST_SHUTDOWN;
                endcase
            end
            ST_FAULT: begin
                if (target_state == ST_POWER_OFF)
                    nxt_state = ST_POWER_OFF;
            end
        endcase
    end

    // Outputs
    assign pd_iso_n    = pd_iso_n_reg;
    assign pd_ret_n    = pd_ret_n_reg;
    assign power_state = cur_state;
    assign busy        = (cur_state != nxt_state) ||
                         (cur_state == ST_POWER_ON) ||
                         (cur_state == ST_INIT);
    assign error       = error_reg;

endmodule
