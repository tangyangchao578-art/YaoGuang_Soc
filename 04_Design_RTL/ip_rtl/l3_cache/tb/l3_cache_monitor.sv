// ============================================================================
// Class: l3_cache_monitor
// Description: L3 Cache Monitor
// Version: 1.0
// ============================================================================

`ifndef L3_CACHE_MONITOR_SV
`define L3_CACHE_MONITOR_SV

class l3_cache_monitor extends uvm_monitor;

    virtual l3_cache_intf      vif;
    uvm_analysis_port#(l3_cache_seq_item) ap;

    l3_cache_config            cfg;

    `uvm_component_utils(l3_cache_monitor)

    function new(string name = "l3_cache_monitor", uvm_component parent = null);
        super.new(name, parent);
        ap = new("ap", this);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual l3_cache_intf)::get(this, "", "vif", vif)) begin
            `uvm_fatal("VIF", "Cannot get vif from config_db")
        end
        if (!uvm_config_db#(l3_cache_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("CFG", "Cannot get cfg from config_db")
        end
    endfunction

    virtual task run_phase(uvm_phase phase);
        fork
            monitor_read_channel();
            monitor_write_channel();
        join
    endtask

    virtual task monitor_read_channel();
        forever begin
            @(posedge vif.clk);
            for (int i = 0; i < cfg.num_masters; i++) begin
                if (vif.saxi_arvalid[i] && vif.saxi_arready[i]) begin
                    l3_cache_seq_item item = l3_cache_seq_item::type_id::create("item");
                    item.is_read = 1;
                    item.addr = vif.saxi_araddr[i];
                    item.len = vif.saxi_arlen[i];
                    item.size = vif.saxi_arsize[i];
                    item.master_id = i;
                    item.delay = $urandom_range(1, 10);
                    `uvm_info("MONITOR", $sformatf("Read request: %s", item.convert2string()), UVM_LOW)
                    ap.write(item);
                end
            end
        end
    endtask

    virtual task monitor_write_channel();
        forever begin
            @(posedge vif.clk);
            for (int i = 0; i < cfg.num_masters; i++) begin
                if (vif.saxi_awvalid[i] && vif.saxi_awready[i]) begin
                    l3_cache_seq_item item = l3_cache_seq_item::type_id::create("item");
                    item.is_read = 0;
                    item.addr = vif.saxi_awaddr[i];
                    item.len = vif.saxi_awlen[i];
                    item.size = vif.saxi_awsize[i];
                    item.data = vif.saxi_wdata[i];
                    item.strb = vif.saxi_wstrb[i];
                    item.master_id = i;
                    item.delay = $urandom_range(1, 10);
                    `uvm_info("MONITOR", $sformatf("Write request: %s", item.convert2string()), UVM_LOW)
                    ap.write(item);
                end
            end
        end
    endtask

endclass

`endif
