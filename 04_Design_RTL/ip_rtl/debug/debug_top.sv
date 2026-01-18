//==============================================================================
// File: debug_top.sv
// Description: Top-level debug module for YaoGuang SoC
//              Integrates JTAG/SWD controllers, CoreSight matrix, 
//              trace aggregator and debug ROM
// Version: 1.0
//==============================================================================

`timescale 1ns/1ps

module debug_top #(
    parameter int NUM_CPUS = 4,
    parameter int NUM_NPUS = 1,
    parameter int TRACE_BUFFER_SIZE = 8192,  // KB
    parameter bit JTAG_EN = 1,
    parameter bit SWD_EN = 1,
    parameter bit TPIU_EN = 1
) (
    // System interfaces
    input  logic                        clk_i,
    input  logic                        rst_ni,
    input  logic                        test_mode_i,
    
    // JTAG interface
    input  logic                        jtag_tck_i,
    input  logic                        jtag_tms_i,
    input  logic                        jtag_tdi_i,
    output logic                        jtag_tdo_o,
    input  logic                        jtag_trst_ni,
    
    // SWD interface
    input  logic                        swd_clk_i,
    inout  logic                        swd_io_b,
    
    // Trace interface
    output logic                        trace_clk_o,
    output logic [31:0]                 trace_data_o,
    output logic                        trace_valid_o,
    output logic                        trace_sync_o,
    
    // System debug control
    input  logic                        dbg_req_i,        // External debug request
    output logic                        dbg_ack_o,        // Debug acknowledge
    output logic [NUM_CPUS-1:0]         cpu_halt_o,       // CPU halt requests
    input  logic [NUM_CPUS-1:0]         cpu_halted_i,     // CPU halted status
    output logic                        sys_reset_req_o,  // System reset request
    
    // AHB debug bus (DAP)
    output logic [31:0]                 haddr_o,
    output logic [2:0]                  hburst_o,
    output logic [3:0]                  hprot_o,
    output logic [2:0]                  hsize_o,
    output logic [1:0]                  htrans_o,
    output logic                        hwrite_o,
    output logic [31:0]                 hwdata_o,
    input  logic                        hready_i,
    input  logic [1:0]                  hresp_i,
    input  logic [31:0]                 hrdata_i,
    
    // CoreSight ATB interface
    output logic [7:0]                  atid_o,
    output logic                        atvalid_o,
    output logic [63:0]                 atdata_o,
    output logic                        atlast_o,
    input  logic                        atready_i,
    
    // Interrupt outputs
    output logic                        debug_int_o,      // Debug event interrupt
    output logic                        trace_full_o,     // Trace buffer full
    output logic                        breakpoint_o,     // Breakpoint hit
    output logic                        watchpoint_o      // Watchpoint hit
);

    //============================================================================
    // Parameters
    //============================================================================
    localparam int DAP_ADDR_WIDTH = 32;
    localparam int DAP_DATA_WIDTH = 32;
    localparam int NUM_AP = 4;
    localparam int JTAG_IR_WIDTH = 5;
    localparam int DEBUG_ROM_SIZE = 1024;
    
    //============================================================================
    // Signal declarations
    //============================================================================
    // DAP interface
    logic [31:0]                 dap_addr;
    logic [31:0]                 dap_wdata;
    logic [3:0]                  dap_be;
    logic                        dap_write;
    logic                        dap_enable;
    logic [31:0]                 dap_rdata;
    logic                        dap_ready;
    logic                        dap_error;
    
    // JTAG signals
    logic [JTAG_IR_WIDTH-1:0]    jtag_ir;
    logic                        jtag_ir_valid;
    logic [31:0]                 jtag_dr_in;
    logic [31:0]                 jtag_dr_out;
    logic                        jtag_dr_valid;
    logic                        jtag_dr_done;
    
    // SWD signals
    logic [31:0]                 swd_addr;
    logic [31:0]                 swd_wdata;
    logic                        swd_write;
    logic                        swd_enable;
    logic [31:0]                 swd_rdata;
    logic                        swd_ready;
    logic                        swd_error;
    
    // Debug request/ack
    logic                        debug_enable;
    logic                        dbg_active;
    logic                        pending_debug_req;
    logic [NUM_CPUS-1:0]         halt_request;
    
    // Trace signals
    logic [7:0]                  trace_atid;
    logic                        trace_atvalid;
    logic [63:0]                 trace_atdata;
    logic                        trace_atlast;
    logic                        trace_atready;
    
    // CPU ETM interfaces
    logic [NUM_CPUS-1:0]         etm_enable;
    logic [NUM_CPUS-1:0][7:0]    etm_atid;
    logic [NUM_CPUS-1:0]         etm_atvalid;
    logic [NUM_CPUS-1:0][63:0]   etm_atdata;
    logic [NUM_CPUS-1:0]         etm_atlast;
    
    // ITM/STM interface
    logic                        itm_enable;
    logic [7:0]                  itm_atid;
    logic                        itm_atvalid;
    logic [63:0]                 itm_atdata;
    logic                        itm_atlast;
    
    // Debug ROM interface
    logic [31:0]                 rom_addr;
    logic [31:0]                 rom_rdata;
    logic                        rom_ready;
    
    // Internal reset
    logic                        rst_n_sync;
    
    //============================================================================
    // Synchronizers
    //============================================================================
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            rst_n_sync <= 1'b0;
        end else begin
            rst_n_sync <= 1'b1;
        end
    end
    
    //============================================================================
    // JTAG Controller (optional)
    //============================================================================
    generate if (JTAG_EN) begin : gen_jtag_ctrl
        jtag_controller #(
            .IR_WIDTH(JTAG_IR_WIDTH)
        ) u_jtag_controller (
            .clk_i(clk_i),
            .rst_ni(rst_n_sync),
            .tck_i(jtag_tck_i),
            .tms_i(jtag_tms_i),
            .tdi_i(jtag_tdi_i),
            .tdo_o(jtag_tdo_o),
            .trst_ni(jtag_trst_ni),
            .ir_o(jtag_ir),
            .ir_valid_o(jtag_ir_valid),
            .dr_in_i(jtag_dr_in),
            .dr_out_o(jtag_dr_out),
            .dr_valid_o(jtag_dr_valid),
            .dr_done_o(jtag_dr_done)
        );
    end else begin : gen_no_jtag
        assign jtag_tdo_o = 1'b0;
        assign jtag_ir = '0;
        assign jtag_ir_valid = '0;
        assign jtag_dr_in = '0;
    end endgenerate
    
    //============================================================================
    // SWD Controller (optional)
    //============================================================================
    generate if (SWD_EN) begin : gen_swd_ctrl
        swd_controller #(
            .ADDR_WIDTH(32)
        ) u_swd_controller (
            .clk_i(clk_i),
            .rst_ni(rst_n_sync),
            .swd_clk_i(swd_clk_i),
            .swd_io_b(swd_io_b),
            .addr_o(swd_addr),
            .wdata_o(swd_wdata),
            .write_o(swd_write),
            .enable_o(swd_enable),
            .rdata_i(swd_rdata),
            .ready_i(swd_ready),
            .error_i(swd_error)
        );
    end else begin : gen_no_swd
        assign swd_addr = '0;
        assign swd_wdata = '0;
        assign swd_write = '0;
        assign swd_enable = '0;
    end endgenerate
    
    //============================================================================
    // DAP (Debug Access Port)
    //============================================================================
    dap_top #(
        .ADDR_WIDTH(DAP_ADDR_WIDTH),
        .DATA_WIDTH(DAP_DATA_WIDTH),
        .NUM_AP(NUM_AP),
        .ROM_SIZE(DEBUG_ROM_SIZE)
    ) u_dap (
        .clk_i(clk_i),
        .rst_ni(rst_n_sync),
        .test_mode_i(test_mode_i),
        
        // JTAG interface
        .jtag_ir_i(jtag_ir),
        .jtag_ir_valid_i(jtag_ir_valid),
        .jtag_dr_in_i(jtag_dr_out),
        .jtag_dr_out_o(jtag_dr_in),
        .jtag_dr_valid_i(jtag_dr_valid),
        .jtag_dr_done_o(jtag_dr_done),
        .jtag_enable_i(JTAG_EN),
        
        // SWD interface
        .swd_addr_i(swd_addr),
        .swd_wdata_i(swd_wdata),
        .swd_write_i(swd_write),
        .swd_enable_i(swd_enable),
        .swd_rdata_o(swd_rdata),
        .swd_ready_o(swd_ready),
        .swd_error_o(swd_error),
        .swd_enable_i(SWD_EN),
        
        // Debug ROM interface
        .rom_addr_o(rom_addr),
        .rom_rdata_i(rom_rdata),
        .rom_ready_i(rom_ready),
        
        // AHB debug bus
        .haddr_o(haddr_o),
        .hburst_o(hburst_o),
        .hprot_o(hprot_o),
        .hsize_o(hsize_o),
        .htrans_o(htrans_o),
        .hwrite_o(hwrite_o),
        .hwdata_o(hwdata_o),
        .hready_i(hready_i),
        .hresp_i(hresp_i),
        .hrdata_i(hrdata_i),
        
        // DAP status and control
        .debug_enable_o(debug_enable),
        .dbg_active_o(dbg_active),
        .halt_request_o(halt_request),
        .cpu_halted_i(cpu_halted_i),
        .sys_reset_req_o(sys_reset_req_o)
    );
    
    //============================================================================
    // Debug ROM
    //============================================================================
    debug_rom #(
        .SIZE(DEBUG_ROM_SIZE),
        .ADDR_WIDTH(32)
    ) u_debug_rom (
        .clk_i(clk_i),
        .rst_ni(rst_n_sync),
        .addr_i(rom_addr),
        .rdata_o(rom_rdata),
        .ready_o(rom_ready)
    );
    
    //============================================================================
    // CoreSight Matrix
    //============================================================================
    coresight_matrix #(
        .NUM_MASTERS(NUM_CPUS + NUM_NPUS + 2),  // CPUs + NPUs + ITM + STM
        .NUM_SLAVES(8),
        .ADDR_WIDTH(32),
        .DATA_WIDTH(64)
    ) u_coresight_matrix (
        .clk_i(clk_i),
        .rst_ni(rst_n_sync),
        
        // Master interfaces (ETMs)
        .m0_atid_i(etm_atid[0]),
        .m0_atvalid_i(etm_atvalid[0]),
        .m0_atdata_i(etm_atdata[0]),
        .m0_atlast_i(etm_atlast[0]),
        .m0_atready_o(),
        
        .m1_atid_i(etm_atid[1]),
        .m1_atvalid_i(etm_atvalid[1]),
        .m1_atdata_i(etm_atdata[1]),
        .m1_atlast_i(etm_atlast[1]),
        .m1_atready_o(),
        
        .m2_atid_i(etm_atid[2]),
        .m2_atvalid_i(etm_atvalid[2]),
        .m2_atdata_i(etm_atdata[2]),
        .m2_atlast_i(etm_atlast[2]),
        .m2_atready_o(),
        
        .m3_atid_i(etm_atid[3]),
        .m3_atvalid_i(etm_atvalid[3]),
        .m3_atdata_i(etm_atdata[3]),
        .m3_atlast_i(etm_atlast[3]),
        .m3_atready_o(),
        
        // ITM interface
        .m4_atid_i(itm_atid),
        .m4_atvalid_i(itm_atvalid),
        .m4_atdata_i(itm_atdata),
        .m4_atlast_i(itm_atlast),
        .m4_atready_o(),
        
        // STM interface (not connected in this version)
        .m5_atid_i('0),
        .m5_atvalid_i('0),
        .m5_atdata_i('0),
        .m5_atlast_i('0),
        .m5_atready_o(),
        
        // TPIU interface
        .s0_atid_o(trace_atid),
        .s0_atvalid_o(trace_atvalid),
        .s0_atdata_o(trace_atdata),
        .s0_atlast_o(trace_atlast),
        .s0_atready_i(trace_atready),
        
        // Trace buffer interface
        .s1_atid_o(),
        .s1_atvalid_o(),
        .s1_atdata_o(),
        .s1_atlast_o(),
        .s1_atready_i(1'b1)
    );
    
    //============================================================================
    // ETM Aggregator
    //============================================================================
    etm_aggregator #(
        .NUM_ETMS(NUM_CPUS),
        .DATA_WIDTH(64)
    ) u_etm_aggregator (
        .clk_i(clk_i),
        .rst_ni(rst_n_sync),
        
        .enable_i(debug_enable),
        
        // ETM inputs
        .etm_enable_o(etm_enable),
        .etm_atid_i(etm_atid),
        .etm_atvalid_i(etm_atvalid),
        .etm_atdata_i(etm_atdata),
        .etm_atlast_i(etm_atlast),
        
        // Aggregated output
        .agg_atid_o(itm_atid),
        .agg_atvalid_o(itm_atvalid),
        .agg_atdata_o(itm_atdata),
        .agg_atlast_o(itm_atlast),
        .agg_atready_i(1'b1)
    );
    
    //============================================================================
    // Trace Buffer
    //============================================================================
    trace_buffer #(
        .SIZE_KB(TRACE_BUFFER_SIZE),
        .DATA_WIDTH(64)
    ) u_trace_buffer (
        .clk_i(clk_i),
        .rst_ni(rst_n_sync),
        
        .enable_i(debug_enable),
        
        // ATB input
        .atid_i(trace_atid),
        .atvalid_i(trace_atvalid),
        .atdata_i(trace_atdata),
        .atlast_i(trace_atlast),
        .atready_o(trace_atready),
        
        // TPIU output
        .tpiu_clk_o(trace_clk_o),
        .tpiu_data_o(trace_data_o),
        .tpiu_valid_o(trace_valid_o),
        .tpiu_sync_o(trace_sync_o),
        
        // Status
        .full_o(trace_full_o),
        .level_o()
    );
    
    //============================================================================
    // Debug Control Logic
    //============================================================================
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            dbg_ack_o <= 1'b0;
            cpu_halt_o <= '0;
            pending_debug_req <= 1'b0;
        end else begin
            // Forward halt requests
            cpu_halt_o <= halt_request;
            
            // Generate debug acknowledge
            dbg_ack_o <= (dbg_active) ? 1'b1 : 1'b0;
            
            // Latch external debug request
            if (dbg_req_i) begin
                pending_debug_req <= 1'b1;
            end else if (dbg_active) begin
                pending_debug_req <= 1'b0;
            end
        end
    end
    
    //============================================================================
    // Interrupt Generation
    //============================================================================
    assign debug_int_o = dbg_active | (|halt_request);
    assign breakpoint_o = |halt_request;
    assign watchpoint_o = 1'b0;  // TODO: Connect from watchpoint unit
    
    //============================================================================
    // Assertions
    //============================================================================
    // JTAG/SWD mutual exclusion (can be both enabled but only one should be used)
    // This is informational only
    
    // Trace buffer size is power of 2
    assert property (@(posedge clk_i) $onehot0(TRACE_BUFFER_SIZE) || (TRACE_BUFFER_SIZE & (TRACE_BUFFER_SIZE - 1)) == 0)
        else $error("Trace buffer size should be power of 2");
    
endmodule
