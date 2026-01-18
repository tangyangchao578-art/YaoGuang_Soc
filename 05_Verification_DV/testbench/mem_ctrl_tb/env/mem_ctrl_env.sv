class mem_ctrl_env extends uvm_env;
    `uvm_component_utils(mem_ctrl_env)
    
    mem_ctrl_agent        mem_ctrl_agt;
    mem_ctrl_scoreboard   mem_ctrl_scb;
    mem_ctrl_coverage     mem_ctrl_cov;
    mem_ctrl_virtual_sequencer virt_seqr;
    
    uvm_tlm_analysis_fifo #(mem_ctrl_transaction) scb_fifo;
    mem_ctrl_config       cfg;
    
    function new(string name = "mem_ctrl_env", uvm_component parent = null);
        super.new(name, parent);
        scb_fifo = new("scb_fifo", this);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if(!uvm_config_db #(mem_ctrl_config)::get(this, "", "mem_ctrl_config", cfg)) begin
            `uvm_error("ENV", "Cannot get mem_ctrl_config from config DB")
        end
        
        mem_ctrl_agt = mem_ctrl_agent::type_id::create("mem_ctrl_agt", this);
        mem_ctrl_scb = mem_ctrl_scoreboard::type_id::create("mem_ctrl_scb", this);
        mem_ctrl_cov = mem_ctrl_coverage::type_id::create("mem_ctrl_cov", this);
        virt_seqr = mem_ctrl_virtual_sequencer::type_id::create("virt_seqr", this);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        mem_ctrl_agt.monitor.item_collected_port.connect(scb_fifo.analysis_export);
        mem_ctrl_scb.item_collected_port.connect(scb_fifo.get_export);
    endfunction
endclass

class mem_ctrl_agent extends uvm_agent;
    `uvm_component_utils(mem_ctrl_agent)
    
    mem_ctrl_agent_config  cfg;
    mem_ctrl_sequencer     seqr;
    mem_ctrl_driver        drv;
    mem_ctrl_monitor       monitor;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if(!uvm_config_db #(mem_ctrl_agent_config)::get(this, "", "cfg", cfg)) begin
            `uvm_error("AGENT", "Cannot get mem_ctrl_agent_config")
        end
        
        monitor = mem_ctrl_monitor::type_id::create("monitor", this);
        
        if(cfg.is_active) begin
            seqr = mem_ctrl_sequencer::type_id::create("seqr", this);
            drv = mem_ctrl_driver::type_id::create("drv", this);
        end
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        if(cfg.is_active) begin
            drv.seq_item_port.connect(seqr.seq_item_export);
        end
    endfunction
endclass

class mem_ctrl_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(mem_ctrl_scoreboard)
    
    uvm_analysis_export #(mem_ctrl_transaction) item_collected_port;
    int passed_count = 0;
    int failed_count = 0;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        item_collected_port = new("item_collected_port", this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            mem_ctrl_transaction tr;
            item_collected_port.peek(tr);
            if(tr.valid) begin
                `uvm_info("SCB", "Memory Transaction Checked", UVM_LOW)
                passed_count++;
            end else begin
                failed_count++;
            end
        end
    endtask
endclass

class mem_ctrl_coverage extends uvm_subscriber #(mem_ctrl_transaction);
    `uvm_component_utils(mem_ctrl_coverage)
    
    covergroup mem_ctrl_cg;
        cp_valid: coverpoint valid { bins valid = {1}; bins invalid = {0}; }
        cp_cmd: coverpoint command { bins read = {0}; bins write = {1}; }
        cp_burst: coverpoint burst_type { bins incr = {0}; bins wrap = {1}; bins fixed = {2}; }
    endgroup
    
    mem_ctrl_transaction tx;
    
    function new(string name = "mem_ctrl_coverage", uvm_component parent = null);
        super.new(name, parent);
        mem_ctrl_cg = new();
    endfunction
    
    virtual function void write(mem_ctrl_transaction t);
        tx = t;
        mem_ctrl_cg.sample();
    endfunction
endclass
