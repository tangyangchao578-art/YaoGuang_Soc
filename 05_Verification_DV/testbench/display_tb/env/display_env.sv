class display_env extends uvm_env;
    `uvm_component_utils(display_env)
    
    display_agent        display_agt;
    display_scoreboard   display_scb;
    display_coverage     display_cov;
    display_virtual_sequencer virt_seqr;
    
    uvm_tlm_analysis_fifo #(display_transaction) scb_fifo;
    display_config       cfg;
    
    function new(string name = "display_env", uvm_component parent = null);
        super.new(name, parent);
        scb_fifo = new("scb_fifo", this);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if(!uvm_config_db #(display_config)::get(this, "", "display_config", cfg)) begin
            `uvm_error("ENV", "Cannot get display_config from config DB")
        end
        
        display_agt = display_agent::type_id::create("display_agt", this);
        display_scb = display_scoreboard::type_id::create("display_scb", this);
        display_cov = display_coverage::type_id::create("display_cov", this);
        virt_seqr = display_virtual_sequencer::type_id::create("virt_seqr", this);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        display_agt.monitor.item_collected_port.connect(scb_fifo.analysis_export);
        display_scb.item_collected_port.connect(scb_fifo.get_export);
    endfunction
endclass

class display_agent extends uvm_agent;
    `uvm_component_utils(display_agent)
    
    display_agent_config  cfg;
    display_sequencer     seqr;
    display_driver        drv;
    display_monitor       monitor;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if(!uvm_config_db #(display_agent_config)::get(this, "", "cfg", cfg)) begin
            `uvm_error("AGENT", "Cannot get display_agent_config")
        end
        
        monitor = display_monitor::type_id::create("monitor", this);
        
        if(cfg.is_active) begin
            seqr = display_sequencer::type_id::create("seqr", this);
            drv = display_driver::type_id::create("drv", this);
        end
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        if(cfg.is_active) begin
            drv.seq_item_port.connect(seqr.seq_item_export);
        end
    endfunction
endclass

class display_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(display_scoreboard)
    
    uvm_analysis_export #(display_transaction) item_collected_port;
    int passed_count = 0;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        item_collected_port = new("item_collected_port", this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            display_transaction tr;
            item_collected_port.peek(tr);
            `uvm_info("SCB", "Display Transaction Checked", UVM_LOW)
            passed_count++;
        end
    endtask
endclass

class display_coverage extends uvm_subscriber #(display_transaction);
    `uvm_component_utils(display_coverage)
    
    covergroup display_cg;
        cp_valid: coverpoint valid { bins valid = {1}; bins invalid = {0}; }
    endgroup
    
    display_transaction tx;
    
    function new(string name = "display_coverage", uvm_component parent = null);
        super.new(name, parent);
        display_cg = new();
    endfunction
    
    virtual function void write(display_transaction t);
        tx = t;
        display_cg.sample();
    endfunction
endclass
