class audio_env extends uvm_env;
    `uvm_component_utils(audio_env)
    
    audio_agent        audio_agt;
    audio_scoreboard   audio_scb;
    audio_coverage     audio_cov;
    audio_virtual_sequencer virt_seqr;
    
    uvm_tlm_analysis_fifo #(audio_transaction) scb_fifo;
    audio_config       cfg;
    
    function new(string name = "audio_env", uvm_component parent = null);
        super.new(name, parent);
        scb_fifo = new("scb_fifo", this);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if(!uvm_config_db #(audio_config)::get(this, "", "audio_config", cfg)) begin
            `uvm_error("ENV", "Cannot get audio_config from config DB")
        end
        
        audio_agt = audio_agent::type_id::create("audio_agt", this);
        audio_scb = audio_scoreboard::type_id::create("audio_scb", this);
        audio_cov = audio_coverage::type_id::create("audio_cov", this);
        virt_seqr = audio_virtual_sequencer::type_id::create("virt_seqr", this);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        audio_agt.monitor.item_collected_port.connect(scb_fifo.analysis_export);
        audio_scb.item_collected_port.connect(scb_fifo.get_export);
    endfunction
endclass

class audio_agent extends uvm_agent;
    `uvm_component_utils(audio_agent)
    
    audio_agent_config  cfg;
    audio_sequencer     seqr;
    audio_driver        drv;
    audio_monitor       monitor;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if(!uvm_config_db #(audio_agent_config)::get(this, "", "cfg", cfg)) begin
            `uvm_error("AGENT", "Cannot get audio_agent_config")
        end
        
        monitor = audio_monitor::type_id::create("monitor", this);
        
        if(cfg.is_active) begin
            seqr = audio_sequencer::type_id::create("seqr", this);
            drv = audio_driver::type_id::create("drv", this);
        end
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        if(cfg.is_active) begin
            drv.seq_item_port.connect(seqr.seq_item_export);
        end
    endfunction
endclass

class audio_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(audio_scoreboard)
    
    uvm_analysis_export #(audio_transaction) item_collected_port;
    int passed_count = 0;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        item_collected_port = new("item_collected_port", this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            audio_transaction tr;
            item_collected_port.peek(tr);
            `uvm_info("SCB", "Audio Transaction Checked", UVM_LOW)
            passed_count++;
        end
    endtask
endclass

class audio_coverage extends uvm_subscriber #(audio_transaction);
    `uvm_component_utils(audio_coverage)
    
    covergroup audio_cg;
        cp_valid: coverpoint valid { bins valid = {1}; bins invalid = {0}; }
        cp_rate: coverpoint sample_rate { 
            bins rates[] = {44100, 48000, 88200, 96000, 192000}; 
        }
    endgroup
    
    audio_transaction tx;
    
    function new(string name = "audio_coverage", uvm_component parent = null);
        super.new(name, parent);
        audio_cg = new();
    endfunction
    
    virtual function void write(audio_transaction t);
        tx = t;
        audio_cg.sample();
    endfunction
endclass
