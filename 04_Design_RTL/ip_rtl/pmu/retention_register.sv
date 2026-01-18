//-----------------------------------------------------------------------------
// Retention Register - Saves/restores critical data during sleep
//-----------------------------------------------------------------------------

`timescale 1ns/1ps

module retention_register (
    input  wire         clk,
    input  wire         rstn,
    input  wire         save_enable,    // Enable save operation
    input  wire         restore_enable, // Enable restore operation
    input  wire [31:0]  save_data,      // Data to save
    output wire [31:0]  restore_data,   // Restored data
    output wire         valid           // Operation valid
);

    // Local Parameters
    localparam NUM_REGS = 16;
    localparam T_SAVE   = 5;
    localparam T_RESTORE = 5;

    // Retention Registers
    reg  [31:0]  retention_mem [0:NUM_REGS-1];
    reg  [3:0]   save_addr;
    reg  [3:0]   restore_addr;
    reg  [31:0]  save_data_reg;
    reg  [31:0]  restore_data_reg;
    reg  [2:0]   save_counter;
    reg  [2:0]   restore_counter;
    reg         save_active;
    reg         restore_active;
    reg         valid_reg;

    // Save Operation
    always @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            save_active    <= 1'b0;
            save_counter   <= '0;
            save_addr      <= '0;
            save_data_reg  <= '0;
        end else if (save_enable && !save_active) begin
            save_active    <= 1'b1;
            save_counter   <= '0;
            save_addr      <= '0;
            save_data_reg  <= save_data;
        end else if (save_active) begin
            if (save_counter < T_SAVE) begin
                save_counter <= save_counter + 1;
            end else begin
                save_counter <= '0;
                if (save_addr < NUM_REGS[3:0]) begin
                    retention_mem[save_addr] <= save_data_reg + save_addr;
                    save_addr <= save_addr + 1;
                end else begin
                    save_active <= 1'b0;
                end
            end
        end
    end

    // Restore Operation
    always @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            restore_active  <= 1'b0;
            restore_counter <= '0;
            restore_addr    <= '0;
            restore_data_reg <= '0;
        end else if (restore_enable && !restore_active) begin
            restore_active  <= 1'b1;
            restore_counter <= '0;
            restore_addr    <= '0;
        end else if (restore_active) begin
            if (restore_counter < T_RESTORE) begin
                restore_counter <= restore_counter + 1;
            end else begin
                restore_counter <= '0;
                if (restore_addr < NUM_REGS[3:0]) begin
                    restore_data_reg <= retention_mem[restore_addr];
                    restore_addr <= restore_addr + 1;
                end else begin
                    restore_active <= 1'b0;
                end
            end
        end
    end

    // Valid Signal
    always @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            valid_reg <= 1'b0;
        end else begin
            valid_reg <= (save_active || restore_active);
        end
    end

    // Restore Data Output
    assign restore_data = restore_data_reg;
    assign valid        = valid_reg;

endmodule
