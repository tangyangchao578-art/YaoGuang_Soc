//-----------------------------------------------------------------------------
// Sleep Controller - Low Power Mode Control and Wake-up Management
//-----------------------------------------------------------------------------

`timescale 1ns/1ps

module sleep_controller (
    input  wire         clk,
    input  wire         rstn,
    input  wire [3:0]   sleep_mode,     // Sleep mode request
    input  wire [4:0]   wake_sources,   // Wake-up sources
    input  wire [4:0]   wake_mask,      // Wake-up mask
    output wire [31:0]  sleep_data,     // Data to save/restore
    output wire         wake_pending,   // Wake-up pending
    input  wire [31:0]  retention_data, // Retention register data
    input  wire         retention_valid // Retention valid
);

    // Local Parameters
    localparam NUM_WAKE = 5;

    // Sleep Mode Definition
    localparam MODE_ACTIVE     = 4'd0;
    localparam MODE_IDLE       = 4'd1;
    localparam MODE_STANDBY    = 4'd2;
    localparam MODE_SLEEP      = 4'd3;
    localparam MODE_DEEP_SLEEP = 4'd4;
    localparam MODE_SHUTDOWN   = 4'd5;

    // Wake-up Sources
    localparam WAKE_GPIO = 0;
    localparam WAKE_RTC  = 1;
    localparam WAKE_CAN  = 2;
    localparam WAKE_USB  = 3;
    localparam WAKE_WDT  = 4;

    // Timing Parameters (in ms)
    localparam T_WAKE_GPIO = 1;   // 100us
    localparam T_WAKE_RTC  = 5;   // 500us
    localparam T_WAKE_CAN  = 2;   // 200us
    localparam T_WAKE_USB  = 3;   // 300us
    localparam T_WAKE_WDT  = 1;   // 50us

    // State Machine
    localparam ST_ACTIVE     = 4'd0;
    localparam ST_IDLE       = 4'd1;
    localparam ST_STANDBY    = 4'd2;
    localparam ST_SLEEP      = 4'd3;
    localparam ST_DEEP_SLEEP = 4'd4;
    localparam ST_SHUTDOWN   = 4'd5;
    localparam ST_WAKING     = 4'd6;

    // Registers
    reg  [3:0]   cur_mode;
    reg  [3:0]   nxt_mode;
    reg  [31:0]  wake_timer;
    reg  [4:0]   wake_source_r;
    reg  [4:0]   wake_source_valid;
    reg         wake_pending_reg;
    reg  [31:0]  sleep_counter;
    reg         timer_active;
    reg  [31:0]  config_reg;

    // Wake-up Detection
    always @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            wake_source_r <= '0;
            wake_source_valid <= '0;
            wake_pending_reg <= 1'b0;
        end else begin
            wake_source_r <= wake_sources;
            wake_source_valid <= wake_sources & ~wake_source_r;
            wake_pending_reg <= |(wake_source_valid & wake_mask);
        end
    end

    // Wake-up Timer
    always @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            wake_timer <= '0;
            timer_active <= 1'b0;
        end else if (timer_active) begin
            wake_timer <= wake_timer - 1;
            if (wake_timer == '0) begin
                timer_active <= 1'b0;
            end
        end else if (wake_pending_reg && (cur_mode != ST_ACTIVE)) begin
            case (cur_mode)
                ST_IDLE:       wake_timer <= T_WAKE_GPIO * 1000;
                ST_STANDBY:    wake_timer <= T_WAKE_RTC * 1000;
                ST_SLEEP:      wake_timer <= T_WAKE_CAN * 1000;
                ST_DEEP_SLEEP: wake_timer <= T_WAKE_USB * 1000;
                ST_SHUTDOWN:   wake_timer <= T_WAKE_WDT * 1000;
                default:       wake_timer <= '0;
            endcase
            timer_active <= 1'b1;
        end
    end

    // Mode State Machine
    always @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            cur_mode <= ST_ACTIVE;
        end else begin
            cur_mode <= nxt_mode;
        end
    end

    // Next State Logic
    always @(*) begin
        nxt_mode = cur_mode;
        case (cur_mode)
            ST_ACTIVE: begin
                case (sleep_mode)
                    MODE_IDLE:       nxt_mode = ST_IDLE;
                    MODE_STANDBY:    nxt_mode = ST_STANDBY;
                    MODE_SLEEP:      nxt_mode = ST_SLEEP;
                    MODE_DEEP_SLEEP: nxt_mode = ST_DEEP_SLEEP;
                    MODE_SHUTDOWN:   nxt_mode = ST_SHUTDOWN;
                    default:         nxt_mode = ST_ACTIVE;
                endcase
            end
            ST_IDLE: begin
                if (wake_pending_reg) nxt_mode = ST_WAKING;
                else if (sleep_mode == MODE_STANDBY) nxt_mode = ST_STANDBY;
            end
            ST_STANDBY: begin
                if (wake_pending_reg) nxt_mode = ST_WAKING;
                else if (sleep_mode == MODE_SLEEP) nxt_mode = ST_SLEEP;
            end
            ST_SLEEP: begin
                if (wake_pending_reg) nxt_mode = ST_WAKING;
                else if (sleep_mode == MODE_DEEP_SLEEP) nxt_mode = ST_DEEP_SLEEP;
            end
            ST_DEEP_SLEEP: begin
                if (wake_pending_reg) nxt_mode = ST_WAKING;
            end
            ST_SHUTDOWN: begin
                if (wake_pending_reg) nxt_mode = ST_WAKING;
            end
            ST_WAKING: begin
                if (!timer_active) nxt_mode = ST_ACTIVE;
            end
        endcase
    end

    // Sleep Data Management
    always @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            sleep_counter <= '0;
        end else begin
            case (cur_mode)
                ST_ACTIVE, ST_WAKING: begin
                    sleep_counter <= '0;
                end
                default: begin
                    sleep_counter <= sleep_counter + 1;
                end
            endcase
        end
    end

    // Sleep Data Output
    assign sleep_data = {24'd0, cur_mode, wake_source_valid};

    // Wake-up Pending
    assign wake_pending = (cur_mode == ST_WAKING) && timer_active;

    // Configuration Register
    always @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            config_reg <= '0;
        end else begin
            config_reg[0] <= 1'b1;  // GPIO wake enable
            config_reg[1] <= 1'b1;  // RTC wake enable
            config_reg[2] <= 1'b1;  // CAN wake enable
            config_reg[3] <= 1'b1;  // USB wake enable
            config_reg[4] <= 1'b1;  // WDT wake enable
            config_reg[8:5] <= sleep_mode;
            config_reg[12:9] <= 4'd3;  // Wake filter delay
        end
    end

endmodule
