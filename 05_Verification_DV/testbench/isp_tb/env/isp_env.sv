class isp_env extends uvm_env;
    `uvm_component_utils(isp_env)
    
    isp_agent        isp_agt;
    isp_scoreboard   isp_scb;
    isp_coverage     isp_cov;
    isp_virtual_sequencer virt_seqr;
    
    uvm_tlm_analysis_fifo #(isp_transaction) scb_fifo;
    isp_config       cfg;
    
    function new(string name = "isp_env", uvm_component parent = null);
        super.new(name, parent);
        scb_fifo = new("scb_fifo", this);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if(!uvm_config_db #(isp_config)::get(this, "", "isp_config", cfg)) begin
            `uvm_error("ENV", "Cannot get isp_config from config DB")
        end
        
        isp_agt = isp_agent::type_id::create("isp_agt", this);
        isp_scb = isp_scoreboard::type_id::create("isp_scb", this);
        isp_cov = isp_coverage::type_id::create("isp_cov", this);
        virt_seqr = isp_virtual_sequencer::type_id::create("virt_seqr", this);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        isp_agt.monitor.item_collected_port.connect(scb_fifo.analysis_export);
        isp_scb.item_collected_port.connect(scb_fifo.get_export);
        virt_seqr.isp_seqr = isp_agt.seqr;
    endfunction
endclass

class isp_agent extends uvm_agent;
    `uvm_component_utils(isp_agent)
    
    isp_agent_config  cfg;
    isp_sequencer     seqr;
    isp_driver        drv;
    isp_monitor       monitor;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if(!uvm_config_db #(isp_agent_config)::get(this, "", "cfg", cfg)) begin
            `uvm_error("AGENT", "Cannot get isp_agent_config")
        end
        
        monitor = isp_monitor::type_id::create("monitor", this);
        
        if(cfg.is_active) begin
            seqr = isp_sequencer::type_id::create("seqr", this);
            drv = isp_driver::type_id::create("drv", this);
        end
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        if(cfg.is_active) begin
            drv.seq_item_port.connect(seqr.seq_item_export);
        end
        monitor.vif = cfg.vif;
        drv.vif = cfg.vif;
    endfunction
endclass

class isp_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(isp_scoreboard)
    
    uvm_analysis_export #(isp_transaction) item_collected_port;
    int passed_count = 0;
    int failed_count = 0;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        item_collected_port = new("item_collected_port", this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            isp_transaction tr;
            item_collected_port.peek(tr);
            process_transaction(tr);
        end
    endtask
    
    virtual protected function void process_transaction(isp_transaction tr);
        if(tr.pixel_valid && tr.processed_valid) begin
            `uvm_info("SCB", $sformatf("ISP Transaction PASSED"), UVM_LOW)
            passed_count++;
        end
    endfunction
endclass

class isp_coverage extends uvm_subscriber #(isp_transaction);
    `uvm_component_utils(isp_coverage)
    
    covergroup isp_cg;
        cp_pix_valid: coverpoint pixel_valid { bins valid = {1}; bins invalid = {0}; }
        cp_proc_valid: coverpoint processed_valid { bins valid = {1}; bins invalid = {0}; }
    endgroup
    
    isp_transaction tx;
    
    function new(string name = "isp_coverage", uvm_component parent = null);
        super.new(name, parent);
        isp_cg = new();
    endfunction
    
    virtual function void write(isp_transaction t);
        tx = t;
        isp_cg.sample();
    endfunction
endclass
