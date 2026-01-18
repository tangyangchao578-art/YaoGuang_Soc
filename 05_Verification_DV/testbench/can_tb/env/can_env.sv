class can_env extends uvm_env;
    `uvm_component_utils(can_env)
    
    can_agent        can_agt;
    can_scoreboard   can_scb;
    can_coverage     can_cov;
    can_virtual_sequencer virt_seqr;
    
    uvm_tlm_analysis_fifo #(can_transaction) scb_fifo;
    can_config       cfg;
    
    function new(string name = "can_env", uvm_component parent = null);
        super.new(name, parent);
        scb_fifo = new("scb_fifo", this);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if(!uvm_config_db #(can_config)::get(this, "", "can_config", cfg)) begin
            `uvm_error("ENV", "Cannot get can_config from config DB")
        end
        
        can_agt = can_agent::type_id::create("can_agt", this);
        can_scb = can_scoreboard::type_id::create("can_scb", this);
        can_cov = can_coverage::type_id::create("can_cov", this);
        virt_seqr = can_virtual_sequencer::type_id::create("virt_seqr", this);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        can_agt.monitor.item_collected_port.connect(scb_fifo.analysis_export);
        can_scb.item_collected_port.connect(scb_fifo.get_export);
    endfunction
endclass

class can_agent extends uvm_agent;
    `uvm_component_utils(can_agent)
    
    can_agent_config  cfg;
    can_sequencer     seqr;
    can_driver        drv;
    can_monitor       monitor;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if(!uvm_config_db #(can_agent_config)::get(this, "", "cfg", cfg)) begin
            `uvm_error("AGENT", "Cannot get can_agent_config")
        end
        
        monitor = can_monitor::type_id::create("monitor", this);
        
        if(cfg.is_active) begin
            seqr = can_sequencer::type_id::create("seqr", this);
            drv = can_driver::type_id::create("drv", this);
        end
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        if(cfg.is_active) begin
            drv.seq_item_port.connect(seqr.seq_item_export);
        end
    endfunction
endclass

class can_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(can_scoreboard)
    
    uvm_analysis_export #(can_transaction) item_collected_port;
    int passed_count = 0;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        item_collected_port = new("item_collected_port", this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            can_transaction tr;
            item_collected_port.peek(tr);
            `uvm_info("SCB", "CAN Transaction Checked", UVM_LOW)
            passed_count++;
        end
    endtask
endclass

class can_coverage extends uvm_subscriber #(can_transaction);
    `uvm_component_utils(can_coverage)
    
    covergroup can_cg;
        cp_tx_valid: coverpoint tx_valid { bins valid = {1}; bins invalid = {0}; }
        cp_rx_valid: coverpoint rx_valid { bins valid = {1}; bins invalid = {0}; }
    endgroup
    
    can_transaction tx;
    
    function new(string name = "can_coverage", uvm_component parent = null);
        super.new(name, parent);
        can_cg = new();
    endfunction
    
    virtual function void write(can_transaction t);
        tx = t;
        can_cg.sample();
    endfunction
endclass
