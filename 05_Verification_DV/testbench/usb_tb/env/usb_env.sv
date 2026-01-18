//-----------------------------------------------------------------------------
// File: usb_env.sv
// Description: USB Controller UVM Environment
//-----------------------------------------------------------------------------
`ifndef USB_ENV_SV
`define USB_ENV_SV

class usb_env extends uvm_env;
    `uvm_component_utils(usb_env)
    
    usb_agent        usb_agt;
    usb_scoreboard   usb_scb;
    usb_coverage     usb_cov;
    usb_virtual_sequencer virt_seqr;
    
    uvm_tlm_analysis_fifo #(usb_transaction) scb_fifo;
    usb_config       cfg;
    
    function new(string name = "usb_env", uvm_component parent = null);
        super.new(name, parent);
        scb_fifo = new("scb_fifo", this);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if(!uvm_config_db #(usb_config)::get(this, "", "usb_config", cfg)) begin
            `uvm_error("ENV", "Cannot get usb_config from config DB")
        end
        
        usb_agt = usb_agent::type_id::create("usb_agt", this);
        uvm_config_db #(usb_agent_config)::set(this, "usb_agt*", "cfg", cfg.agent_cfg);
        
        usb_scb = usb_scoreboard::type_id::create("usb_scb", this);
        usb_cov = usb_coverage::type_id::create("usb_cov", this);
        virt_seqr = usb_virtual_sequencer::type_id::create("virt_seqr", this);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        usb_agt.monitor.item_collected_port.connect(scb_fifo.analysis_export);
        usb_scb.item_collected_port.connect(scb_fifo.get_export);
        usb_cov.item_collected_port.connect(scb_fifo.get_export);
        
        virt_seqr.usb_seqr = usb_agt.seqr;
    endfunction
endclass

`endif
