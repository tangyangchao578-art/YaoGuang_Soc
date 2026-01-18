class usb_base_test extends uvm_test;
    `uvm_component_utils(usb_base_test)
    
    usb_env env;
    usb_config cfg;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        cfg = usb_config::type_id::create("cfg");
        cfg.agent_cfg = usb_agent_config::type_id::create("agent_cfg");
        if(!uvm_config_db #(virtual usb_if)::get(this, "", "usb_vif", cfg.agent_cfg.vif)) begin
            `uvm_error("TEST", "Cannot get usb_vif from config DB")
        end
        uvm_config_db #(usb_config)::set(this, "*", "usb_config", cfg);
        
        env = usb_env::type_id::create("env", this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        #1ms;
        phase.drop_objection(this);
    endtask
endclass

class usb_basic_test extends usb_base_test;
    `uvm_component_utils(usb_basic_test)
    
    virtual task run_phase(uvm_phase phase);
        usb_basic_seq seq;
        
        phase.raise_objection(this);
        seq = usb_basic_seq::type_id::create("seq");
        seq.start(env.virt_seqr.usb_seqr);
        phase.drop_objection(this);
    endtask
endclass
