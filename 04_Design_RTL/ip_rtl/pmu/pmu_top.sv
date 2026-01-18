//-----------------------------------------------------------------------------
// PMU Top Module - Power Management Unit Top Level
// YaoGuang SoC
//-----------------------------------------------------------------------------

`timescale 1ns/1ps

module pmu_top (
    // APB Interface
    input  wire         pclk,
    input  wire         presetn,
    input  wire [31:0]  paddr,
    input  wire         pwrite,
    input  wire [31:0]  pwdata,
    input  wire         penable,
    input  wire [3:0]   pstrb,
    output wire [31:0]  prdata,
    output wire         pslverr,

    // Clock & Reset
    input  wire         clk_fast,
    input  wire         clk_slow,
    input  wire         rstn_fast,
    input  wire         rstn_slow,
    input  wire         por_n,

    // Power Domain Control Outputs
    output wire [9:0]   pd_enable,      // Power domain enable
    output wire [9:0]   pd_iso_n,       // Power domain isolation
    output wire [9:0]   pd_ret_n,       // Power domain retention
    output wire [9:0]   pd_clk_gate,    // Power domain clock gate

    // Voltage Regulator Control
    output wire [15:0]  vreg_ctrl,      // Voltage regulator control
    input  wire [15:0]  vreg_status,    // Voltage regulator status

    // Voltage Monitor Inputs
    input  wire [9:0]   vmon_valid,     // Voltage monitor valid
    input  wire [31:0]  vmon_data,      // Voltage monitor data (10 channels x 32-bit)

    // Temperature Monitor Inputs
    input  wire [7:0]   tmon_valid,     // Temperature monitor valid
    input  wire [31:0]  tmon_data,      // Temperature monitor data (8 channels x 32-bit)

    // Current Monitor Inputs
    input  wire [4:0]   imon_valid,     // Current monitor valid
    input  wire [31:0]  imon_data,      // Current monitor data (5 channels x 32-bit)

    // DVFS Control Outputs
    output wire [3:0]   dvfs_cpu_level, // CPU DVFS level (0-15)
    output wire [3:0]   dvfs_npu_level, // NPU DVFS level (0-15)
    output wire [3:0]   dvfs_gpu_level, // GPU DVFS level (0-15)
    output wire [7:0]   dvfs_volt_ctrl, // DVFS voltage control

    // Wake-up Inputs
    input  wire         wake_gpio,      // GPIO wake-up
    input  wire         wake_rtc,       // RTC wake-up
    input  wire         wake_can,       // CAN wake-up
    input  wire         wake_usb,       // USB wake-up
    input  wire         wake_wdt,       // Watchdog wake-up

    // Interrupt Outputs
    output wire         irq_voltage,    // Voltage alarm interrupt
    output wire         irq_temp,       // Temperature alarm interrupt
    output wire         irq_power,      // Power budget interrupt
    output wire         irq_state,      // Power state change interrupt
    output wire         irq_wdt,        // Watchdog interrupt

    // Status Outputs
    output wire [3:0]   power_state,    // Current power state
    output wire         pmu_busy,       // PMU busy indicator
    output wire         pmu_error,      // PMU error indicator
    output wire [31:0]  pmu_status      // PMU status register
);

    // Local Parameters
    localparam NUM_PD      = 10;
    localparam NUM_VMON    = 10;
    localparam NUM_TMON    = 8;
    localparam NUM_IMON    = 5;
    localparam NUM_WAKE    = 5;

    // State Machine Encoding
    localparam ST_POWER_OFF    = 4'h0;
    localparam ST_POWER_ON     = 4'h1;
    localparam ST_INIT         = 4'h2;
    localparam ST_ACTIVE       = 4'h3;
    localparam ST_IDLE         = 4'h4;
    localparam ST_STANDBY      = 4'h5;
    localparam ST_SLEEP        = 4'h6;
    localparam ST_DEEP_SLEEP   = 4'h7;
    localparam ST_SHUTDOWN     = 4'h8;
    localparam ST_FAULT        = 4'hF;

    // Internal Signals
    reg  [3:0]   cur_state;
    reg  [3:0]   nxt_state;
    reg  [31:0]  control_reg;
    reg  [31:0]  status_reg;
    reg  [31:0]  intr_reg;
    reg  [31:0]  intr_mask;
    reg  [31:0]  wdt_counter;
    reg          wdt_enable;
    reg  [15:0]  wdt_timeout;
    reg  [31:0]  power_consumption;
    reg  [31:0]  power_budget;
    reg  [9:0]   pd_request;
    reg  [3:0]   dvfs_request;

    // APB Interface Signals
    wire         apb_sel;
    wire [31:0]  apb_rdata;
    wire         apb_ready;
    wire         apb_slverr;

    // Sub-module Instantiations
    wire [3:0]   sm_power_state;
    wire [9:0]   sm_pd_enable;
    wire [9:0]   sm_pd_iso_n;
    wire [9:0]   sm_pd_ret_n;
    wire [3:0]   sm_dvfs_level;
    wire         sm_busy;
    wire         sm_error;

    wire [31:0]  pm_power_data;
    wire [15:0]  pm_alarm_flags;

    wire [31:0]  sc_sleep_data;
    wire         sc_wake_pending;

    wire [31:0]  rc_retention_data;
    wire         rc_retention_valid;

    // Wake-up Source Register
    reg  [NUM_WAKE-1:0] wake_sources;
    reg  [NUM_WAKE-1:0] wake_mask;
    reg                 wake_any;

    // Fault Detection
    reg  [3:0]  fault_count;
    reg         over_voltage;
    reg         under_voltage;
    reg         over_temp;
    reg         over_current;

    // APB Slave Logic
    assign apb_sel = penable;
    assign pslverr = apb_slverr;
    assign prdata  = apb_rdata;

    always @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            cur_state <= ST_POWER_OFF;
        end else begin
            cur_state <= nxt_state;
        end
    end

    always @(*) begin
        nxt_state = cur_state;
        case (cur_state)
            ST_POWER_OFF: begin
                if (control_reg[0]) nxt_state = ST_POWER_ON;
            end
            ST_POWER_ON: begin
                if (!sm_busy) nxt_state = ST_INIT;
            end
            ST_INIT: begin
                if (!sm_busy) nxt_state = ST_ACTIVE;
            end
            ST_ACTIVE: begin
                case (control_reg[2:1])
                    2'b00: nxt_state = ST_ACTIVE;
                    2'b01: nxt_state = ST_IDLE;
                    2'b10: nxt_state = ST_STANDBY;
                    2'b11: nxt_state = ST_SLEEP;
                endcase
            end
            ST_IDLE: begin
                if (wake_any) nxt_state = ST_ACTIVE;
                else if (control_reg[3]) nxt_state = ST_STANDBY;
            end
            ST_STANDBY: begin
                if (wake_any) nxt_state = ST_ACTIVE;
                else if (control_reg[4]) nxt_state = ST_SLEEP;
            end
            ST_SLEEP: begin
                if (wake_any) nxt_state = ST_ACTIVE;
                else if (control_reg[5]) nxt_state = ST_DEEP_SLEEP;
            end
            ST_DEEP_SLEEP: begin
                if (wake_any) nxt_state = ST_ACTIVE;
            end
            ST_SHUTDOWN: begin
                if (wake_any) nxt_state = ST_POWER_ON;
            end
            ST_FAULT: begin
                if (control_reg[7]) nxt_state = ST_POWER_OFF;
            end
            default: nxt_state = cur_state;
        endcase
    end

    // Power Domain Controller Instance
    power_domain_controller u_power_domain_controller (
        .clk            (clk_fast),
        .rstn           (rstn_fast),
        .pd_request     (pd_request),
        .pd_enable      (sm_pd_enable),
        .pd_iso_n       (sm_pd_iso_n),
        .pd_ret_n       (sm_pd_ret_n),
        .pd_clk_gate    (pd_clk_gate),
        .vreg_ctrl      (vreg_ctrl),
        .vreg_status    (vreg_status),
        .busy           (sm_busy),
        .error          (sm_error)
    );

    // Power State Machine Instance
    power_state_machine u_power_state_machine (
        .clk            (clk_fast),
        .rstn           (rstn_fast),
        .target_state   (control_reg[3:0]),
        .pd_enable      (sm_pd_enable),
        .pd_iso_n       (sm_pd_iso_n),
        .pd_ret_n       (sm_pd_ret_n),
        .power_state    (sm_power_state),
        .busy           (sm_busy),
        .error          (sm_error)
    );

    // DVFS Controller Instance
    dvfs_controller u_dvfs_controller (
        .clk            (clk_fast),
        .rstn           (rstn_fast),
        .dvfs_request   (dvfs_request),
        .cpu_level      (dvfs_cpu_level),
        .npu_level      (dvfs_npu_level),
        .gpu_level      (dvfs_gpu_level),
        .volt_ctrl      (dvfs_volt_ctrl),
        .power_state    (sm_power_state),
        .busy           (),
        .error          ()
    );

    // Power Monitor Instance
    power_monitor u_power_monitor (
        .clk            (clk_slow),
        .rstn           (rstn_slow),
        .vmon_valid     (vmon_valid),
        .vmon_data      (vmon_data),
        .tmon_valid     (tmon_valid),
        .tmon_data      (tmon_data),
        .imon_valid     (imon_valid),
        .imon_data      (imon_data),
        .power_data     (pm_power_data),
        .alarm_flags    (pm_alarm_flags),
        .budget         (power_budget),
        .consumption    (power_consumption)
    );

    // Sleep Controller Instance
    sleep_controller u_sleep_controller (
        .clk            (clk_slow),
        .rstn           (rstn_slow),
        .sleep_mode     (control_reg[5:2]),
        .wake_sources   (wake_sources),
        .wake_mask      (wake_mask),
        .sleep_data     (sc_sleep_data),
        .wake_pending   (sc_wake_pending),
        .retention_data (rc_retention_data),
        .retention_valid(rc_retention_valid)
    );

    // Retention Register Instance
    retention_register u_retention_register (
        .clk            (clk_slow),
        .rstn           (rstn_slow),
        .save_enable    (control_reg[8]),
        .restore_enable (control_reg[9]),
        .save_data      (sc_sleep_data),
        .restore_data   (rc_retention_data),
        .valid          (rc_retention_valid)
    );

    // Wake-up Source Processing
    always @(posedge clk_slow or negedge rstn_slow) begin
        if (!rstn_slow) begin
            wake_sources <= '0;
            wake_any     <= 1'b0;
        end else begin
            wake_sources[0] <= wake_gpio;
            wake_sources[1] <= wake_rtc;
            wake_sources[2] <= wake_can;
            wake_sources[3] <= wake_usb;
            wake_sources[4] <= wake_wdt;
            wake_any <= (| (wake_sources & wake_mask));
        end
    end

    // Watchdog Timer
    always @(posedge clk_slow or negedge rstn_slow) begin
        if (!rstn_slow) begin
            wdt_counter <= '0;
            wdt_enable  <= 1'b0;
        end else begin
            if (control_reg[10]) begin
                wdt_enable <= 1'b1;
                if (wdt_counter >= wdt_timeout) begin
                    wdt_counter <= '0;
                    if (wdt_enable) begin
                        nxt_state = ST_FAULT;
                        intr_reg[4] = 1'b1;
                    end
                end else begin
                    wdt_counter <= wdt_counter + 1;
                end
            end else if (control_reg[11]) begin
                wdt_counter <= '0;
            end else begin
                wdt_enable <= control_reg[10];
            end
        end
    end

    // Fault Detection
    always @(posedge clk_slow or negedge rstn_slow) begin
        if (!rstn_slow) begin
            over_voltage  <= 1'b0;
            under_voltage <= 1'b0;
            over_temp     <= 1'b0;
            over_current  <= 1'b0;
            fault_count   <= '0;
        end else begin
            over_voltage  <= |(pm_alarm_flags[3:0]);
            under_voltage <= |(pm_alarm_flags[7:4]);
            over_temp     <= |(pm_alarm_flags[11:8]);
            over_current  <= |(pm_alarm_flags[15:12]);

            if (over_voltage || under_voltage || over_temp || over_current) begin
                if (fault_count < 4'hF) fault_count <= fault_count + 1;
                if (fault_count >= 4'hE) begin
                    nxt_state = ST_FAULT;
                end
            end else begin
                fault_count <= '0;
            end
        end
    end

    // Interrupt Generation
    assign irq_voltage = intr_reg[0] & intr_mask[0];
    assign irq_temp    = intr_reg[1] & intr_mask[1];
    assign irq_power  = intr_reg[2] & intr_mask[2];
    assign irq_state  = intr_reg[3] & intr_mask[3];
    assign irq_wdt    = intr_reg[4] & intr_mask[4];

    // Status Outputs
    assign power_state = sm_power_state;
    assign pmu_busy    = sm_busy;
    assign pmu_error   = sm_error;
    assign pmu_status  = {28'd0, fault_count[3:0]};

    // APB Register Map
    always @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            control_reg    <= '0;
            status_reg     <= '0;
            intr_reg       <= '0;
            intr_mask      <= '0;
            wdt_timeout    <= 16'd1000;
            power_budget   <= 32'd60000;
            wake_mask      <= '1;
            pd_request     <= '0;
            dvfs_request   <= '0;
        end else if (apb_sel && pwrite && penable) begin
            case (paddr[11:2])
                10'h000: control_reg    <= pwdata;
                10'h001: status_reg     <= pwdata;
                10'h002: intr_reg       <= pwdata;
                10'h003: intr_mask      <= pwdata;
                10'h004: wdt_timeout    <= pwdata[15:0];
                10'h005: power_budget   <= pwdata;
                10'h006: wake_mask      <= pwdata[NUM_WAKE-1:0];
                10'h007: pd_request     <= pwdata[9:0];
                10'h008: dvfs_request   <= pwdata[3:0];
                default: ;
            endcase
        end else begin
            intr_reg[0] <= pm_alarm_flags[0] | over_voltage;
            intr_reg[1] <= pm_alarm_flags[1] | over_temp;
            intr_reg[2] <= (power_consumption > power_budget);
            intr_reg[3] <= (cur_state != nxt_state);
            intr_reg[4] <= 1'b0;
        end
    end

    assign apb_ready = 1'b1;
    assign apb_slverr = 1'b0;

    always @(*) begin
        apb_rdata = '0;
        case (paddr[11:2])
            10'h000: apb_rdata = control_reg;
            10'h001: apb_rdata = status_reg;
            10'h002: apb_rdata = intr_reg;
            10'h003: apb_rdata = intr_mask;
            10'h004: apb_rdata = {16'd0, wdt_timeout};
            10'h005: apb_rdata = power_budget;
            10'h006: apb_rdata = {27'd0, wake_mask};
            10'h007: apb_rdata = {22'd0, pd_request};
            10'h008: apb_rdata = {28'd0, dvfs_request};
            10'h010: apb_rdata = pm_power_data;
            10'h011: apb_rdata = power_consumption;
            10'h012: apb_rdata = {28'd0, sm_power_state, 4'd0, fault_count};
            10'h020: apb_rdata = {24'd0, vmon_data[7:0]};
            10'h021: apb_rdata = {24'd0, tmon_data[7:0]};
            default: apb_rdata = '0;
        endcase
    end

endmodule
