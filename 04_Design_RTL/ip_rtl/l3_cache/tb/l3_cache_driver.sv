// ============================================================================
// Class: l3_cache_driver
// Description: L3 Cache Driver
// Version: 1.0
// ============================================================================

`ifndef L3_CACHE_DRIVER_SV
`define L3_CACHE_DRIVER_SV

class l3_cache_driver extends uvm_driver#(l3_cache_seq_item);

    virtual l3_cache_intf      vif;
    l3_cache_config            cfg;

    `uvm_component_utils(l3_cache_driver)

    function new(string name = "l3_cache_driver", uvm_component parent = null);
        super.new(name, parent);
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
            reset_driver();
            drive_transactions();
        join
    endtask

    virtual task reset_driver();
        forever begin
            @(negedge vif.rst_n);
            `uvm_info("DRIVER", "Reset asserted", UVM_LOW)
            wait (vif.rst_n);
        end
    endtask

    virtual task drive_transactions();
        forever begin
            seq_item_port.get_next_item(req);
            drive_item(req);
            seq_item_port.item_done();
        end
    endtask

    virtual task drive_item(l3_cache_seq_item item);
        // 等待延迟
        #(item.delay * 1ns);

        if (item.is_read) begin
            drive_read(item);
        end else begin
            drive_write(item);
        end
    endtask

    virtual task drive_read(l3_cache_seq_item item);
        // 发起读请求
        vif.saxi_arvalid[item.master_id] <= 1;
        vif.saxi_araddr[item.master_id] <= item.addr;
        vif.saxi_arlen[item.master_id] <= item.len;
        vif.saxi_arsize[item.master_id] <= item.size;
        vif.saxi_arburst[item.master_id] <= 2'b01;  // INCR
        vif.saxi_arqos[item.master_id] <= 4'b0;

        wait (vif.saxi_arready[item.master_id]);
        @(posedge vif.clk);
        vif.saxi_arvalid[item.master_id] <= 0;

        // 等待读响应
        while (!vif.saxi_rvalid[item.master_id]) begin
            @(posedge vif.clk);
        end

        // 采样响应
        item.rdata = vif.saxi_rdata[item.master_id];
        item.resp = vif.saxi_rresp[item.master_id];
        item.rlast = vif.saxi_rlast[item.master_id];

        @(posedge vif.clk);
        vif.saxi_rready[item.master_id] <= 1;
        @(posedge vif.clk);
        vif.saxi_rready[item.master_id] <= 0;

        `uvm_info("DRIVER", $sformatf("Read completed: addr=0x%08h data=0x%064h", item.addr, item.rdata), UVM_LOW)
    endtask

    virtual task drive_write(l3_cache_seq_item item);
        // 发起写请求
        vif.saxi_awvalid[item.master_id] <= 1;
        vif.saxi_awaddr[item.master_id] <= item.addr;
        vif.saxi_awlen[item.master_id] <= item.len;
        vif.saxi_awsize[item.master_id] <= item.size;
        vif.saxi_awburst[item.master_id] <= 2'b01;  // INCR
        vif.saxi_awqos[item.master_id] <= 4'b0;

        wait (vif.saxi_awready[item.master_id]);
        @(posedge vif.clk);
        vif.saxi_awvalid[item.master_id] <= 0;

        // 发送写数据
        for (int i = 0; i <= item.len; i++) begin
            vif.saxi_wvalid[item.master_id] <= 1;
            vif.saxi_wdata[item.master_id] <= item.data;
            vif.saxi_wstrb[item.master_id] <= item.strb;
            vif.saxi_wlast[item.master_id] <= (i == item.len);
            wait (vif.saxi_wready[item.master_id]);
            @(posedge vif.clk);
        end
        vif.saxi_wvalid[item.master_id] <= 0;

        // 等待写响应
        while (!vif.saxi_bvalid[item.master_id]) begin
            @(posedge vif.clk);
        end
        item.resp = vif.saxi_bresp[item.master_id];

        @(posedge vif.clk);
        vif.saxi_bready[item.master_id] <= 1;
        @(posedge vif.clk);
        vif.saxi_bready[item.master_id] <= 0;

        `uvm_info("DRIVER", $sformatf("Write completed: addr=0x%08h", item.addr), UVM_LOW)
    endtask

endclass

`endif
