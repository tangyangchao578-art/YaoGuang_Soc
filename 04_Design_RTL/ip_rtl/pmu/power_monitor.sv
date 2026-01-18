//-----------------------------------------------------------------------------
// Power Monitor - Voltage, Temperature, and Current Monitoring
//-----------------------------------------------------------------------------

`timescale 1ns/1ps

module power_monitor (
    input  wire         clk,
    input  wire         rstn,
    input  wire [9:0]   vmon_valid,     // Voltage monitor valid
    input  wire [31:0]  vmon_data,      // Voltage monitor data (10 channels)
    input  wire [7:0]   tmon_valid,     // Temperature monitor valid
    input  wire [31:0]  tmon_data,      // Temperature monitor data (8 channels)
    input  wire [4:0]   imon_valid,     // Current monitor valid
    input  wire [31:0]  imon_data,      // Current monitor data (5 channels)
    output wire [31:0]  power_data,     // Power consumption data
    output wire [15:0]  alarm_flags,    // Alarm flags
    input  wire [31:0]  budget,         // Power budget
    output wire [31:0]  consumption     // Current power consumption
);

    // Local Parameters
    localparam NUM_VMON   = 10;
    localparam NUM_TMON   = 8;
    localparam NUM_IMON   = 5;

    // Threshold Configuration
    localparam VOLT_HIGH  = 32'd1050;   // 1.05V (mV)
    localparam VOLT_LOW   = 32'd650;    // 0.65V (mV)
    localparam TEMP_HIGH  = 32'd110;    // 110°C
    localparam TEMP_CRIT  = 32'd125;    // 125°C
    localparam CURRENT_HIGH = 32'd15000; // 15A (mA)

    // Voltage Channel Mapping
    localparam VCPU   = 3'd0;
    localparam VSAFETY = 3'd1;
    localparam VNPU   = 3'd2;
    localparam VGPU   = 3'd3;
    localparam VNOC   = 3'd4;
    localparam VMEM   = 3'd5;
    localparam VSYS   = 3'd6;
    localparam VIO    = 3'd7;
    localparam VANA   = 3'd8;
    localparam VRTC   = 3'd9;

    // Temperature Channel Mapping
    localparam TCPU   = 3'd0;
    localparam TNP    = 3'd1;
    localparam TGP    = 3'd2;
    localparam TNC    = 3'd3;
    localparam TMEM   = 3'd4;
    localparam TIO    = 3'd5;
    localparam TPMU   = 3'd6;
    localparam TEXT   = 3'd7;

    // Current Channel Mapping
    localparam ICPU   = 2'd0;
    localparam INPU   = 2'd1;
    localparam IGP    = 2'd2;
    localparam IMEM   = 2'd3;
    localparam IIO    = 2'd4;

    // Threshold Registers
    reg  [31:0]  volt_thresh_high [0:NUM_VMON-1];
    reg  [31:0]  volt_thresh_low  [0:NUM_VMON-1];
    reg  [31:0]  temp_thresh_high [0:NUM_TMON-1];
    reg  [31:0]  temp_thresh_crit [0:NUM_TMON-1];
    reg  [31:0]  curr_thresh_high [0:NUM_IMON-1];

    // Monitored Values
    reg  [31:0]  volt_values [0:NUM_VMON-1];
    reg  [31:0]  temp_values [0:NUM_TMON-1];
    reg  [31:0]  curr_values [0:NUM_IMON-1];

    // Alarm Registers
    reg  [9:0]   volt_alarm_high;
    reg  [9:0]   volt_alarm_low;
    reg  [7:0]   temp_alarm_high;
    reg  [7:0]   temp_alarm_crit;
    reg  [4:0]   curr_alarm_high;

    // Power Calculation
    reg  [31:0]  total_power;
    reg  [31:0]  dynamic_power;
    reg  [31:0]  static_power;

    // Integration Counter
    reg  [31:0]  sample_counter;
    reg  [63:0]  power_integrator;
    reg          power_valid;

    // Initialize Thresholds
    integer i;
    initial begin
        for (i = 0; i < NUM_VMON; i = i + 1) begin
            volt_thresh_high[i] = VOLT_HIGH;
            volt_thresh_low[i]  = VOLT_LOW;
        end
        for (i = 0; i < NUM_TMON; i = i + 1) begin
            temp_thresh_high[i] = TEMP_HIGH;
            temp_thresh_crit[i] = TEMP_CRIT;
        end
        for (i = 0; i < NUM_IMON; i = i + 1) begin
            curr_thresh_high[i] = CURRENT_HIGH;
        end
    end

    // Voltage Monitoring
    genvar v_idx;
    generate for (v_idx = 0; v_idx < NUM_VMON; v_idx = v_idx + 1) begin: V_MON
        always @(posedge clk or negedge rstn) begin
            if (!rstn) begin
                volt_values[v_idx] <= '0;
                volt_alarm_high[v_idx] <= 1'b0;
                volt_alarm_low[v_idx] <= 1'b0;
            end else if (vmon_valid[v_idx]) begin
                volt_values[v_idx] <= vmon_data[v_idx*32 +: 32];
                volt_alarm_high[v_idx] <= (vmon_data[v_idx*32 +: 32] > volt_thresh_high[v_idx]);
                volt_alarm_low[v_idx]  <= (vmon_data[v_idx*32 +: 32] < volt_thresh_low[v_idx]);
            end
        end
    end endgenerate

    // Temperature Monitoring
    genvar t_idx;
    generate for (t_idx = 0; t_idx < NUM_TMON; t_idx = t_idx + 1) begin: T_MON
        always @(posedge clk or negedge rstn) begin
            if (!rstn) begin
                temp_values[t_idx] <= '0;
                temp_alarm_high[t_idx] <= 1'b0;
                temp_alarm_crit[t_idx] <= 1'b0;
            end else if (tmon_valid[t_idx]) begin
                temp_values[t_idx] <= tmon_data[t_idx*32 +: 32];
                temp_alarm_high[t_idx] <= (tmon_data[t_idx*32 +: 32] > temp_thresh_high[t_idx]);
                temp_alarm_crit[t_idx] <= (tmon_data[t_idx*32 +: 32] > temp_thresh_crit[t_idx]);
            end
        end
    end endgenerate

    // Current Monitoring
    genvar c_idx;
    generate for (c_idx = 0; c_idx < NUM_IMON; c_idx = c_idx + 1) begin: I_MON
        always @(posedge clk or negedge rstn) begin
            if (!rstn) begin
                curr_values[c_idx] <= '0;
                curr_alarm_high[c_idx] <= 1'b0;
            end else if (imon_valid[c_idx]) begin
                curr_values[c_idx] <= imon_data[c_idx*32 +: 32];
                curr_alarm_high[c_idx] <= (imon_data[c_idx*32 +: 32] > curr_thresh_high[c_idx]);
            end
        end
    end endgenerate

    // Power Calculation (P = V * I)
    always @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            power_integrator <= '0;
            sample_counter    <= '0;
            power_valid       <= 1'b0;
            total_power       <= '0;
        end else begin
            sample_counter <= sample_counter + 1;

            if (sample_counter >= 1000) begin
                sample_counter <= '0;
                total_power <= power_integrator[63:32] / 1000;
                power_integrator <= '0;
                power_valid <= 1'b1;
            end else begin
                power_valid <= 1'b0;
                power_integrator <= power_integrator +
                    {32'd0, volt_values[VCPU]} * {32'd0, curr_values[ICPU]} / 1000000 +
                    {32'd0, volt_values[VNPU]} * {32'd0, curr_values[INPU]} / 1000000 +
                    {32'd0, volt_values[VGPU]} * {32'd0, curr_values[IGP]} / 1000000 +
                    {32'd0, volt_values[VMEM]} * {32'd0, curr_values[IMEM]} / 1000000 +
                    {32'd0, volt_values[VIO]}  * {32'd0, curr_values[IIO]}  / 1000000;
            end
        end
    end

    // Static Power Estimation (based on voltage and temperature)
    always @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            static_power <= 32'd5000;  // 5W default
        end else begin
            static_power <= 32'd5000 +
                (temp_values[TCPU] > 80) ? 32'd1000 : 32'd0 +
                (temp_values[TNP] > 80)  ? 32'd2000 : 32'd0 +
                (temp_values[TGP] > 80)  ? 32'd700 : 32'd0;
        end
    end

    // Dynamic Power Calculation
    always @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            dynamic_power <= '0;
        end else begin
            dynamic_power <=
                volt_values[VCPU] * curr_values[ICPU] / 1000000 +
                volt_values[VNPU] * curr_values[INPU] / 1000000 +
                volt_values[VGPU] * curr_values[IGP] / 1000000 +
                volt_values[VMEM] * curr_values[IMEM] / 1000000 +
                volt_values[VIO]  * curr_values[IIO]  / 1000000;
        end
    end

    // Total Power
    always @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            consumption <= '0;
        end else begin
            consumption <= dynamic_power + (static_power >> 2);
        end
    end

    // Alarm Flags
    assign alarm_flags[0]  = |volt_alarm_high;   // Over voltage
    assign alarm_flags[1]  = |volt_alarm_low;    // Under voltage
    assign alarm_flags[2]  = |temp_alarm_high;   // Temperature warning
    assign alarm_flags[3]  = |temp_alarm_crit;   // Temperature critical
    assign alarm_flags[4]  = |curr_alarm_high;   // Over current
    assign alarm_flags[15:5] = '0;

    // Power Data Output
    assign power_data = {consumption[31:16], static_power[15:0]};

endmodule
