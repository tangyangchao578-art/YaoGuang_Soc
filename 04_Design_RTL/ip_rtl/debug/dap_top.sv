//==============================================================================
// File: dap_top.sv
// Description: Debug Access Port (DAP) Top
//              Implements CoreSight DAP with APB/AP/AXI access ports
// Version: 1.0
//==============================================================================

`timescale 1ns/1ps

module dap_top #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int NUM_AP = 4,
    parameter int ROM_SIZE = 1024
) (
    // System interface
    input  logic                        clk_i,
    input  logic                        rst_ni,
    input  logic                        test_mode_i,
    
    // JTAG interface
    input  logic [4:0]                  jtag_ir_i,
    input  logic                        jtag_ir_valid_i,
    input  logic [31:0]                 jtag_dr_in_i,
    output logic [31:0]                 jtag_dr_out_o,
    input  logic                        jtag_dr_valid_i,
    output logic                        jtag_dr_done_o,
    input  logic                        jtag_enable_i,
    
    // SWD interface
    input  logic [ADDR_WIDTH-1:0]       swd_addr_i,
    input  logic [DATA_WIDTH-1:0]       swd_wdata_i,
    input  logic                        swd_write_i,
    input  logic                        swd_enable_i,
    output logic [DATA_WIDTH-1:0]       swd_rdata_o,
    output logic                        swd_ready_o,
    output logic                        swd_error_o,
    input  logic                        swd_enable_i2,
    
    // Debug ROM interface
    output logic [31:0]                 rom_addr_o,
    input  logic [31:0]                 rom_rdata_i,
    input  logic                        rom_ready_i,
    
    // AHB debug bus
    output logic [ADDR_WIDTH-1:0]       haddr_o,
    output logic [2:0]                  hburst_o,
    output logic [3:0]                  hprot_o,
    output logic [2:0]                  hsize_o,
    output logic [1:0]                  htrans_o,
    output logic                        hwrite_o,
    output logic [DATA_WIDTH-1:0]       hwdata_o,
    input  logic                        hready_i,
    input  logic [1:0]                  hresp_i,
    input  logic [DATA_WIDTH-1:0]       hrdata_i,
    
    // Debug control
    output logic                        debug_enable_o,
    output logic                        dbg_active_o,
    output logic [3:0]                  halt_request_o,
    input  logic [3:0]                  cpu_halted_i,
    output logic                        sys_reset_req_o
);

    //============================================================================
    // Parameters
    //============================================================================
    localparam int IDCODE = 32'hBA00477;  // YaoGuang Chip ID
    localparam int NUM_AP_W = $clog2(NUM_AP+1);
    
    //============================================================================
    // Signal declarations
    //============================================================================
    // DP registers
    typedef enum logic [3:0] {
        REG_IDCODE   = 4'h0,
        REG_CTRL     = 4'h4,
        REG_STATUS   = 4'h8,
        REG_RESEND   = 4'hC,
        REG_SELECT   = 4'h10,
        REG_RDBUFF   = 4'h14,
        REG_TARGETID = 4'h18,
        REG_DLPID    = 4'h1C
    } dp_reg_t;
    
    // AP registers
    typedef enum logic [3:0] {
        AP_REG_CSW = 4'h0,
        AP_REG_TAR = 4'h4,
        AP_REG_DRW = 4'hC,
        AP_REG_BD0 = 4'h10,
        AP_REG_BD1 = 4'h14,
        AP_REG_BD2 = 4'h18,
        AP_REG_BD3 = 4'h1C
    } ap_reg_t;
    
    // Current register access
    logic [3:0]           dp_reg_addr;
    logic [31:0]          dp_rdata;
    logic                 dp_reg_valid;
    
    logic [3:0]           ap_reg_addr;
    logic [31:0]          ap_rdata;
    logic                 ap_reg_valid;
    logic                 ap_access;
    
    // DP state
    logic [31:0]          ctrl_reg;
    logic [31:0]          status_reg;
    logic [3:0]           select_reg;  // [7:4] = AP selection, [3:0] = DP bank
    logic [NUM_AP_W-1:0]  selected_ap;
    logic [3:0]           selected_bank;
    
    // APB-AP state
    logic                 apb_enable;
    logic [31:0]          apb_addr;
    logic [31:0]          apb_wdata;
    logic                 apb_write;
    logic                 apb_ready;
    logic [31:0]          apb_rdata;
    logic                 apb_error;
    
    // Transaction state
    logic                 transaction_active;
    logic                 transaction_write;
    logic                 transaction_error;
    logic [31:0]          transaction_data;
    logic                 transaction_done;
    
    // Halt control
    logic [3:0]           halt_request;
    logic                 halt_ack;
    logic                 dbg_active;
    
    // JTAG/SWD interface mux
    logic                 use_jtag;
    logic                 use_swd;
    logic [31:0]          jtag_addr, swd_addr;
    logic [31:0]          jtag_wdata, swd_wdata;
    logic                 jtag_write, swd_write;
    logic                 jtag_enable, swd_enable;
    logic [31:0]          jtag_rdata, swd_rdata;
    logic                 jtag_ready, swd_ready;
    logic                 jtag_error, swd_error;
    
    //============================================================================
    // Interface Multiplexing
    //============================================================================
    assign use_jtag = jtag_enable_i;
    assign use_swd = swd_enable_i2;
    
    assign jtag_addr = {24'b0, jtag_dr_in_i[31:24]};  // Extract address from DR
    assign jtag_wdata = jtag_dr_in_i;
    assign jtag_write = jtag_dr_in_i[21];  // RNW bit
    assign jtag_enable = jtag_dr_valid_i && (jtag_ir_i == 5'b10010);  // DEBUG instruction
    
    assign swd_addr = swd_addr_i;
    assign swd_wdata = swd_wdata_i;
    assign swd_write = swd_write_i;
    assign swd_enable = swd_enable_i;
    
    // Mux outputs
    always_comb begin
        if (use_jtag) begin
            jtag_rdata = apb_rdata;
            jtag_ready = apb_ready;
            jtag_error = apb_error;
            jtag_dr_out_o = apb_rdata;
            jtag_dr_done_o = transaction_done;
        end else begin
            jtag_rdata = '0;
            jtag_ready = '0;
            jtag_error = '0;
        end
        
        if (use_swd) begin
            swd_rdata_o = apb_rdata;
            swd_ready_o = apb_ready;
            swd_error_o = apb_error;
        end else begin
            swd_rdata_o = '0;
            swd_ready_o = '0;
            swd_error_o = '0;
        end
    end
    
    //============================================================================
    // DP Register Access
    //============================================================================
    // Address decoding for DP registers
    always_comb begin
        dp_reg_addr = '0;
        dp_reg_valid = 1'b0;
        
        if (use_jtag || use_swd) begin
            logic [7:0] addr_byte;
            if (use_jtag) addr_byte = jtag_dr_in_i[31:24];
            else addr_byte = swd_addr[7:0];
            
            unique casez (addr_byte)
                8'h00: begin dp_reg_addr = REG_IDCODE; dp_reg_valid = 1'b1; end
                8'h04: begin dp_reg_addr = REG_CTRL; dp_reg_valid = 1'b1; end
                8'h08: begin dp_reg_addr = REG_STATUS; dp_reg_valid = 1'b1; end
                8'h0C: begin dp_reg_addr = REG_RESEND; dp_reg_valid = 1'b1; end
                8'h10: begin dp_reg_addr = REG_SELECT; dp_reg_valid = 1'b1; end
                8'h14: begin dp_reg_addr = REG_RDBUFF; dp_reg_valid = 1'b1; end
                8'h18: begin dp_reg_addr = REG_TARGETID; dp_reg_valid = 1'b1; end
                8'h1C: begin dp_reg_addr = REG_DLPID; dp_reg_valid = 1'b1; end
                default: dp_reg_valid = 1'b0;
            endcase
        end
    end
    
    // DP register read
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            dp_rdata <= '0;
        end else if (dp_reg_valid && !jtag_write && !swd_write) begin
            case (dp_reg_addr)
                REG_IDCODE:   dp_rdata <= IDCODE;
                REG_CTRL:     dp_rdata <= ctrl_reg;
                REG_STATUS:   dp_rdata <= status_reg;
                REG_RESEND:   dp_rdata <= transaction_data;
                REG_SELECT:   dp_rdata <= {28'b0, select_reg};
                REG_RDBUFF:   dp_rdata <= apb_rdata;
                REG_TARGETID: dp_rdata <= IDCODE;
                REG_DLPID:    dp_rdata <= 32'h0BA00477;
                default:      dp_rdata <= '0;
            endcase
        end
    end
    
    // DP register write
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            ctrl_reg <= '0;
            select_reg <= '0;
        end else if (dp_reg_valid && (jtag_write || swd_write)) begin
            logic [31:0] wdata = use_jtag ? jtag_dr_in_i : swd_wdata;
            
            case (dp_reg_addr)
                REG_CTRL: begin
                    ctrl_reg <= wdata;
                end
                REG_SELECT: begin
                    select_reg <= wdata[7:0];
                    selected_ap <= wdata[7:4];
                    selected_bank <= wdata[3:0];
                end
                default: begin
                    // No action
                end
            endcase
        end
    end
    
    //============================================================================
    // AP Access (APB-AP)
    //============================================================================
    // AP register address decoding
    always_comb begin
        ap_reg_addr = '0;
        ap_reg_valid = 1'b0;
        
        if (use_jtag || use_swd) begin
            logic [7:0] addr_byte;
            if (use_jtag) addr_byte = jtag_dr_in_i[31:24];
            else addr_byte = swd_addr[7:0];
            
            // AP access if APnDP = 1 (bit 1 of request)
            if (use_jtag ? jtag_dr_in_i[19] : swd_addr[1]) begin
                ap_access = 1'b1;
                
                unique casez (addr_byte[3:0])
                    4'h0: begin ap_reg_addr = AP_REG_CSW; ap_reg_valid = 1'b1; end
                    4'h4: begin ap_reg_addr = AP_REG_TAR; ap_reg_valid = 1'b1; end
                    4'hC: begin ap_reg_addr = AP_REG_DRW; ap_reg_valid = 1'b1; end
                    4'h0: begin ap_reg_addr = AP_REG_BD0; ap_reg_valid = 1'b1; end
                    4'h4: begin ap_reg_addr = AP_REG_BD1; ap_reg_valid = 1'b1; end
                    4'h8: begin ap_reg_addr = AP_REG_BD2; ap_reg_valid = 1'b1; end
                    4'hC: begin ap_reg_addr = AP_REG_BD3; ap_reg_valid = 1'b1; end
                    default: ap_reg_valid = 1'b0;
                endcase
            end else begin
                ap_access = 1'b0;
            end
        end else begin
            ap_access = 1'b0;
        end
    end
    
    // APB-AP state machine
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            apb_enable <= 1'b0;
            apb_addr <= '0;
            apb_wdata <= '0;
            apb_write <= 1'b0;
            transaction_active <= 1'b0;
            transaction_done <= 1'b0;
        end else begin
            transaction_done <= 1'b0;
            
            if (!transaction_active) begin
                // Start new transaction
                if (ap_reg_valid) begin
                    apb_enable <= 1'b1;
                    apb_write <= (use_jtag ? jtag_dr_in_i[20] : swd_write);
                    
                    if (use_jtag) begin
                        // JTAG: Address in DR[23:12]
                        apb_addr <= {jtag_dr_in_i[31:12], 4'b0};
                        apb_wdata <= jtag_dr_in_i;
                    end else begin
                        // SWD: Full address
                        apb_addr <= swd_addr;
                        apb_wdata <= swd_wdata;
                    end
                    transaction_active <= 1'b1;
                    transaction_write <= apb_write;
                end
            end else begin
                // Transaction in progress
                if (apb_ready) begin
                    apb_enable <= 1'b0;
                    transaction_active <= 1'b0;
                    transaction_done <= 1'b1;
                end
            end
        end
    end
    
    // APB-AP ready/error
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            apb_rdata <= '0;
            apb_error <= 1'b0;
            apb_ready <= 1'b0;
        end else begin
            if (apb_enable) begin
                // Simulate APB access completion
                if (apb_ready) begin
                    apb_rdata <= hrdata_i;
                    apb_error <= hresp_i[1];  // ERROR response
                end
            end else begin
                apb_ready <= 1'b0;
            end
        end
    end
    
    //============================================================================
    // AHB Output Assignments
    //============================================================================
    assign haddr_o = apb_addr;
    assign hwrite_o = apb_write;
    assign hwdata_o = apb_wdata;
    assign hsize_o = 3'b010;  // 32-bit
    assign htrans_o = apb_enable ? 2'b10 : 2'b00;  // NONSEQ when active
    assign hburst_o = 3'b000;  // Single
    assign hprot_o = 4'b0011;  // Data access, privileged
    
    // Simulate AHB ready (for simulation)
    assign hready_i = 1'b1;  // In real design, this comes from fabric
    assign hresp_i = 2'b00;  // OKAY
    
    //============================================================================
    // Debug Control
    //============================================================================
    assign debug_enable_o = ctrl_reg[0];  // DBGEN
    assign dbg_active_o = dbg_active;
    
    // Halt request generation
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            halt_request <= '0;
            dbg_active <= 1'b0;
        end else begin
            // Generate halt requests from debug enable
            if (ctrl_reg[0]) begin
                halt_request <= halt_request;
                
                // Check if any CPU halted
                if ((|cpu_halted_i) && (|halt_request)) begin
                    dbg_active <= 1'b1;
                end
            end else begin
                halt_request <= '0;
                dbg_active <= 1'b0;
            end
        end
    end
    
    assign halt_request_o = halt_request;
    assign sys_reset_req_o = ctrl_reg[4];  // SYSREQRST
    
    //============================================================================
    // Status Register
    //============================================================================
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            status_reg <= '0;
        end else begin
            status_reg <= {
                20'b0,           // Reserved
                1'b0,            // WDATAERR (write data error)
                1'b0,            // READOK (read data ready)
                1'b0,            // STICKYERR (sticky error)
                1'b0,            // STICKYCMP (sticky compare)
                1'b0,            // TINITPRES (init present)
                1'b0,            // TINITOK (init OK)
                1'b0,            // TFIFO mode
                1'b1,            // Power up
                1'b0,            // Reset
                2'b00            // Mode
            };
        end
    end
    
    //============================================================================
    // Assertions
    //============================================================================
    initial begin
        if (NUM_AP < 1) begin
            $error("NUM_AP must be at least 1");
        end
    end
    
    // Transaction completion check
    assert property (@(posedge clk_i) disable iff (!rst_ni)
        apb_enable |-> apb_ready)
        else $warning("APB access may not complete");
    
endmodule
