//-----------------------------------------------------------------------------
// Safety Island Top-level Testbench
// YaoGuang SoC ASIL-D Safety Module Verification
// Top-level module that instantiates the UVM environment
//-----------------------------------------------------------------------------
`timescale 1ns/1ps

module safety_island_tb;
    import uvm_pkg::*;
    import safety_island_pkg::*;
    
    // Clock and Reset
    bit clk;
    bit rst_n;
    
    // Interface instance
    safety_island_if si_if(clk, rst_n);
    
    // DUT instance (placeholder - replace with actual RTL)
    safety_island_dut dut (
        .clk(clk),
        .rst_n(rst_n),
        .opcode(si_if.opcode),
        .data(si_if.data),
        .addr(si_if.addr),
        .id(si_if.id),
        .valid(si_if.valid),
        .ready(si_if.ready),
        .resp(si_if.resp),
        .status(si_if.status),
        .error(si_if.error),
        .lockstep_match(si_if.lockstep_match),
        .ecc_status(si_if.ecc_status),
        .wdg_timeout(si_if.wdg_timeout)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // Reset generation
    initial begin
        rst_n = 0;
        #100 rst_n = 1;
    end
    
    // Configuration
    initial begin
        uvm_config_db#(virtual safety_island_if)::set(null, "*", "vif", si_if);
        run_test();
    end
    
    // Simulation timeout
    initial begin
        #100000 $finish;
    end
    
endmodule

// Placeholder DUT module - replace with actual RTL
module safety_island_dut(
    input bit clk,
    input bit rst_n,
    output logic[7:0] opcode,
    output logic[31:0] data,
    output logic[31:0] addr,
    output logic[7:0] id,
    input bit valid,
    output bit ready,
    input bit[1:0] resp,
    input bit[31:0] status,
    output bit error,
    input bit lockstep_match,
    input bit[5:0] ecc_status,
    input bit wdg_timeout
);
    // Placeholder implementation
    always @(posedge clk or negedge rst_n) begin
        if(!rst_n) begin
            ready <= 1'b0;
            error <= 1'b0;
        end else begin
            ready <= valid;
            error <= 1'b0;
        end
    end
endmodule
