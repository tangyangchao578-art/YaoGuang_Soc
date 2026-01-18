//-----------------------------------------------------------------------------
// Power Domain Controller
// Controls power domain enable, isolation, retention, and clock gating
//-----------------------------------------------------------------------------

`timescale 1ns/1ps

module power_domain_controller (
    input  wire         clk,
    input  wire         rstn,
    input  wire [9:0]   pd_request,     // Power domain request
    output wire [9:0]   pd_enable,      // Power domain enable
    output wire [9:0]   pd_iso_n,       // Power domain isolation (active low)
    output wire [9:0]   pd_ret_n,       // Power domain retention (active low)
    output wire [9:0]   pd_clk_gate,    // Power domain clock gate
    output wire [15:0]  vreg_ctrl,      // Voltage regulator control
    input  wire [15:0]  vreg_status,    // Voltage regulator status
    output wire         busy,
    output wire         error
);

    // Local Parameters
    localparam NUM_PD = 10;

    // State Machine
    localparam ST_IDLE      = 4'h0;
    localparam ST_POWER_ON  = 4'h1;
    localparam ST_WAIT_VREG = 4'h2;
    localparam ST_ENABLE    = 4'h3;
    localparam ST_RELEASE   = 4'h4;
    localparam ST_POWER_OFF = 4'h5;
    localparam ST_RETENTION = 4'h6;

    // Timing Parameters (in cycles @ clk)
    localparam T_VREG_RAMP  = 100;      // Voltage regulator ramp time
    localparam T_ENABLE     = 10;       // Enable settling time
    localparam T_ISOLATION  = 5;        // Isolation settling time
    localparam T_RETENTION  = 20;       // Retention save/restore time
    localparam T_SEQ_DELAY  = 50;       // Sequence delay between domains

    // Registers
    reg  [3:0]   cur_state;
    reg  [3:0]   nxt_state;
    reg  [9:0]   pd_enable_reg;
    reg  [9:0]   pd_iso_n_reg;
    reg  [9:0]   pd_ret_n_reg;
    reg  [9:0]   pd_clk_gate_reg;
    reg  [15:0]  vreg_ctrl_reg;
    reg  [31:0]  timer;
    reg  [3:0]   seq_counter;
    reg  [9:0]   pending_request;
    reg          sequence_active;

    // State Machine
    always @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            cur_state <= ST_IDLE;
            pd_enable_reg <= '0;
            pd_iso_n_reg <= '1;        // Isolation disabled (high)
            pd_ret_n_reg <= '1;        // Retention disabled (high)
            pd_clk_gate_reg <= '0;     // Clock gated
            vreg_ctrl_reg <= 16'd1000; // Default 1.0V
            timer <= '0;
            seq_counter <= '0;
            pending_request <= '0;
            sequence_active <= 1'b0;
        end else begin
            cur_state <= nxt_state;
            case (nxt_state)
                ST_IDLE: begin
                    if (|pd_request) begin
                        pending_request <= pd_request;
                        sequence_active <= 1'b1;
                        seq_counter <= '0;
                    end
                end
                ST_POWER_ON: begin
                    timer <= '0;
                    if (seq_counter < 4'd9) begin
                        if (pending_request[seq_counter]) begin
                            pd_enable_reg[seq_counter] <= 1'b1;
                            vreg_ctrl_reg <= 16'd1000;
                        end
                        seq_counter <= seq_counter + 1;
                    end
                end
                ST_WAIT_VREG: begin
                    timer <= timer + 1;
                end
                ST_ENABLE: begin
                    timer <= timer + 1;
                    pd_iso_n_reg <= '0;     // Enable isolation
                end
                ST_RELEASE: begin
                    timer <= timer + 1;
                    pd_clk_gate_reg[seq_counter] <= 1'b1;
                    if (timer >= T_ENABLE) begin
                        sequence_active <= 1'b0;
                    end
                end
                ST_POWER_OFF: begin
                    pd_clk_gate_reg[seq_counter] <= 1'b0;
                    pd_iso_n_reg <= '1;
                    pd_ret_n_reg <= '1;
                    pd_enable_reg[seq_counter] <= 1'b0;
                    if (timer >= T_ENABLE) begin
                        if (seq_counter < 4'd9) begin
                            seq_counter <= seq_counter + 1;
                        end else begin
                            sequence_active <= 1'b0;
                        end
                    end else begin
                        timer <= timer + 1;
                    end
                end
                ST_RETENTION: begin
                    timer <= timer + 1;
                    pd_ret_n_reg <= '0;      // Enable retention
                    if (timer >= T_RETENTION) begin
                        sequence_active <= 1'b0;
                    end
                end
            endcase
        end
    end

    // Next State Logic
    always @(*) begin
        nxt_state = cur_state;
        case (cur_state)
            ST_IDLE: begin
                if (sequence_active) begin
                    nxt_state = ST_POWER_ON;
                end
            end
            ST_POWER_ON: begin
                if (&pd_enable_reg) begin
                    nxt_state = ST_WAIT_VREG;
                end
            end
            ST_WAIT_VREG: begin
                if (timer >= T_VREG_RAMP) begin
                    nxt_state = ST_ENABLE;
                end
            end
            ST_ENABLE: begin
                if (timer >= T_ENABLE) begin
                    nxt_state = ST_RELEASE;
                end
            end
            ST_RELEASE: begin
                if (timer >= T_ENABLE) begin
                    nxt_state = ST_IDLE;
                end
            end
            ST_POWER_OFF: begin
                if (!sequence_active) begin
                    nxt_state = ST_IDLE;
                end
            end
            ST_RETENTION: begin
                if (timer >= T_RETENTION) begin
                    nxt_state = ST_IDLE;
                end
            end
        endcase
    end

    // Outputs
    assign pd_enable   = pd_enable_reg;
    assign pd_iso_n    = pd_iso_n_reg;
    assign pd_ret_n    = pd_ret_n_reg;
    assign pd_clk_gate = pd_clk_gate_reg;
    assign vreg_ctrl   = vreg_ctrl_reg;
    assign busy        = sequence_active;
    assign error       = 1'b0;

endmodule
