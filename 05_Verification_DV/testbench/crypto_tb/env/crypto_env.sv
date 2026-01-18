class crypto_env extends uvm_env;
    `uvm_component_utils(crypto_env)
    
    crypto_agent        crypto_agt;
    crypto_scoreboard   crypto_scb;
    crypto_coverage     crypto_cov;
    crypto_virtual_sequencer virt_seqr;
    
    uvm_tlm_analysis_fifo #(crypto_transaction) scb_fifo;
    crypto_config       cfg;
    
    function new(string name = "crypto_env", uvm_component parent = null);
        super.new(name, parent);
        scb_fifo = new("scb_fifo", this);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if(!uvm_config_db #(crypto_config)::get(this, "", "crypto_config", cfg)) begin
            `uvm_error("ENV", "Cannot get crypto_config from config DB")
        end
        
        crypto_agt = crypto_agent::type_id::create("crypto_agt", this);
        crypto_scb = crypto_scoreboard::type_id::create("crypto_scb", this);
        crypto_cov = crypto_coverage::type_id::create("crypto_cov", this);
        virt_seqr = crypto_virtual_sequencer::type_id::create("virt_seqr", this);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        crypto_agt.monitor.item_collected_port.connect(scb_fifo.analysis_export);
        crypto_scb.item_collected_port.connect(scb_fifo.get_export);
    endfunction
endclass

class crypto_agent extends uvm_agent;
    `uvm_component_utils(crypto_agent)
    
    crypto_agent_config  cfg;
    crypto_sequencer     seqr;
    crypto_driver        drv;
    crypto_monitor       monitor;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if(!uvm_config_db #(crypto_agent_config)::get(this, "", "cfg", cfg)) begin
            `uvm_error("AGENT", "Cannot get crypto_agent_config")
        end
        
        monitor = crypto_monitor::type_id::create("monitor", this);
        
        if(cfg.is_active) begin
            seqr = crypto_sequencer::type_id::create("seqr", this);
            drv = crypto_driver::type_id::create("drv", this);
        end
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        if(cfg.is_active) begin
            drv.seq_item_port.connect(seqr.seq_item_export);
        end
    endfunction
endclass

class crypto_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(crypto_scoreboard)
    
    uvm_analysis_export #(crypto_transaction) item_collected_port;
    int passed_count = 0;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        item_collected_port = new("item_collected_port", this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            crypto_transaction tr;
            item_collected_port.peek(tr);
            `uvm_info("SCB", "Crypto Transaction Checked", UVM_LOW)
            passed_count++;
        end
    endtask
endclass

class crypto_coverage extends uvm_subscriber #(crypto_transaction);
    `uvm_component_utils(crypto_coverage)
    
    covergroup crypto_cg;
        cp_valid: coverpoint valid { bins valid = {1}; bins invalid = {0}; }
        cp_algo: coverpoint algorithm { bins aes = {0}; bins sha = {1}; bins rsa = {2}; }
    endgroup
    
    crypto_transaction tx;
    
    function new(string name = "crypto_coverage", uvm_component parent = null);
        super.new(name, parent);
        crypto_cg = new();
    endfunction
    
    virtual function void write(crypto_transaction t);
        tx = t;
        crypto_cg.sample();
    endfunction
endclass
