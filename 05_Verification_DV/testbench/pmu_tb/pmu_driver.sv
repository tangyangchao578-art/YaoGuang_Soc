`ifndef PMU_DRIVER_SV
`define PMU_DRIVER_SV

class pmu_driver extends uvm_driver#(pmu_seq_item);
    `uvm_component_utils(pmu_driver)

    virtual pmu_if   vif;

    function new(string name = "pmu_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual pmu_if)::get(this, "", "pmu_if", vif)) begin
            `uvm_fatal(get_name(), "Cannot get pmu_if from config DB")
        end
    endfunction

    task run_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(req);
            drive_item(req);
            seq_item_port.item_done();
        end
    endtask

    virtual task drive_item(pmu_seq_item req);
        vif.op_type       <= req.op_type;
        vif.power_domain  <= req.power_domain;
        vif.voltage_level <= req.voltage_level;
        vif.frequency     <= req.frequency;
        vif.timeout_val   <= req.timeout_val;
        vif.protect_en    <= req.protect_enable;
        vif.start_cmd     <= 1'b1;

        wait(vif.done == 1'b1);
        @(posedge vif.clk);
        vif.start_cmd     <= 1'b0;
        @(posedge vif.clk);
    endtask
endclass

`endif
