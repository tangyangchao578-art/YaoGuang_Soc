//-----------------------------------------------------------------------------
// DVFS Controller - Dynamic Voltage Frequency Scaling
//-----------------------------------------------------------------------------

`timescale 1ns/1ps

module dvfs_controller (
    input  wire         clk,
    input  wire         rstn,
    input  wire [3:0]   dvfs_request,   // DVFS level request
    output wire [3:0]   cpu_level,      // CPU DVFS level
    output wire [3:0]   npu_level,      // NPU DVFS level
    output wire [3:0]   gpu_level,      // GPU DVFS level
    output wire [7:0]   volt_ctrl,      // Voltage control
    input  wire [3:0]   power_state,    // Current power state
    output wire         busy,
    output wire         error
);

    // Local Parameters
    localparam NUM_LEVELS = 16;

    // DVFS Level Configuration (Frequency in MHz, Voltage in mV)
    localparam [15:0] FREQ_TABLE [0:15] = '{
        16'd500,   // Level 0: 500 MHz
        16'd600,   // Level 1: 600 MHz
        16'd700,   // Level 2: 700 MHz
        16'd800,   // Level 3: 800 MHz
        16'd900,   // Level 4: 900 MHz
        16'd1000,  // Level 5: 1.0 GHz
        16'd1100,  // Level 6: 1.1 GHz
        16'd1200,  // Level 7: 1.2 GHz
        16'd1300,  // Level 8: 1.3 GHz
        16'd1400,  // Level 9: 1.4 GHz
        16'd1500,  // Level 10: 1.5 GHz
        16'd1600,  // Level 11: 1.6 GHz
        16'd1700,  // Level 12: 1.7 GHz
        16'd1800,  // Level 13: 1.8 GHz
        16'd1900,  // Level 14: 1.9 GHz
        16'd2000   // Level 15: 2.0 GHz
    };

    localparam [15:0] VOLT_TABLE [0:15] = '{
        16'd700,   // Level 0: 0.70V
        16'd720,   // Level 1: 0.72V
        16'd740,   // Level 2: 0.74V
        16'd760,   // Level 3: 0.76V
        16'd780,   // Level 4: 0.78V
        16'd800,   // Level 5: 0.80V
        16'd820,   // Level 6: 0.82V
        16'd840,   // Level 7: 0.84V
        16'd860,   // Level 8: 0.86V
        16'd880,   // Level 9: 0.88V
        16'd900,   // Level 10: 0.90V
        16'd920,   // Level 11: 0.92V
        16'd940,   // Level 12: 0.94V
        16'd960,   // Level 13: 0.96V
        16'd980,   // Level 14: 0.98V
        16'd1000   // Level 15: 1.00V
    };

    // Timing Parameters
    localparam T_FREQ_CHANGE = 100;     // Frequency change settling
    localparam T_VOLT_CHANGE = 200;     // Voltage change settling

    // Registers
    reg  [3:0]   cur_cpu_level;
    reg  [3:0]   cur_npu_level;
    reg  [3:0]   cur_gpu_level;
    reg  [3:0]   target_cpu_level;
    reg  [3:0]   target_npu_level;
    reg  [3:0]   target_gpu_level;
    reg  [15:0]  timer;
    reg  [1:0]   change_phase;          // 0=idle, 1=voltage, 2=frequency, 3=done
    reg          scaling_active;
    reg  [3:0]   last_request;

    // DVFS Policy Logic
    always @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            target_cpu_level <= 4'd8;  // Default mid-level
            target_npu_level <= 4'd8;
            target_gpu_level <= 4'd6;
        end else if (dvfs_request != last_request) begin
            last_request <= dvfs_request;
            case (dvfs_request)
                4'h0: begin          // Low power
                    target_cpu_level <= 4'd2;
                    target_npu_level <= 4'd2;
                    target_gpu_level <= 4'd1;
                end
                4'h1: begin          // Power save
                    target_cpu_level <= 4'd4;
                    target_npu_level <= 4'd4;
                    target_gpu_level <= 4'd3;
                end
                4'h2: begin          // Balanced
                    target_cpu_level <= 4'd8;
                    target_npu_level <= 4'd8;
                    target_gpu_level <= 4'd6;
                end
                4'h3: begin          // Performance
                    target_cpu_level <= 4'd12;
                    target_npu_level <= 4'd12;
                    target_gpu_level <= 4'd10;
                end
                4'h4: begin          // High performance
                    target_cpu_level <= 4'd15;
                    target_npu_level <= 4'd15;
                    target_gpu_level <= 4'd12;
                end
                default: begin       // Auto mode
                    target_cpu_level <= 4'd8;
                    target_npu_level <= 4'd8;
                    target_gpu_level <= 4'd6;
                end
            endcase
        end
    end

    // Scaling State Machine
    always @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            cur_cpu_level  <= 4'd2;
            cur_npu_level  <= 4'd2;
            cur_gpu_level  <= 4'd1;
            timer          <= '0;
            change_phase   <= 2'd0;
            scaling_active <= 1'b0;
        end else begin
            if (!scaling_active && (target_cpu_level != cur_cpu_level ||
                                    target_npu_level != cur_npu_level ||
                                    target_gpu_level != cur_gpu_level)) begin
                scaling_active <= 1'b1;
                timer <= '0;
                change_phase <= 2'd1;
            end

            case (change_phase)
                2'd0: begin  // Idle
                    if (scaling_active) begin
                        scaling_active <= 1'b0;
                    end
                end
                2'd1: begin  // Voltage change
                    timer <= timer + 1;
                    if (timer >= T_VOLT_CHANGE) begin
                        timer <= '0;
                        change_phase <= 2'd2;
                    end
                end
                2'd2: begin  // Frequency change
                    timer <= timer + 1;
                    if (timer >= T_FREQ_CHANGE) begin
                        timer <= '0;
                        change_phase <= 2'd3;
                        cur_cpu_level <= target_cpu_level;
                        cur_npu_level <= target_npu_level;
                        cur_gpu_level <= target_gpu_level;
                    end
                end
                2'd3: begin  // Done
                    timer <= timer + 1;
                    if (timer >= 10) begin
                        change_phase <= 2'd0;
                    end
                end
            endcase
        end
    end

    // Outputs
    assign cpu_level = (power_state >= 4'd4) ? 4'd0 : cur_cpu_level;
    assign npu_level = (power_state >= 4'd4) ? 4'd0 : cur_npu_level;
    assign gpu_level = (power_state >= 4'd4) ? 4'd0 : cur_gpu_level;

    // Voltage control based on highest level
    assign volt_ctrl[7:0] = (power_state >= 4'd4) ? 8'd0 : VOLT_TABLE[cur_cpu_level];

    assign busy  = scaling_active;
    assign error = 1'b0;

endmodule
