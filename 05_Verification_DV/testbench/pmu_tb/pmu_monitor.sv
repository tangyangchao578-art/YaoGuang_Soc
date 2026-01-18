`ifndef PMU_MONITOR_SV
`define PMU_MONITOR_SV

class pmu_monitor extends uvm_monitor;
    `uvm_component_utils(pmu_monitor)

    uvm_analysis_port#(pmu_seq_item) ap;
    virtual pmu_if   vif;
    pmu_seq_item     trans;

    function new(string name = "pmu_monitor", uvm_component parent = null);
        super.new(name, parent);
        ap = new("ap", this);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual pmu_if)::get(this, "", "pmu_if", vif)) begin
            `uvm_fatal(get_name(), "Cannot get pmu_if from config DB")
        end
    endfunction

    task run_phase(uvm_phase phase);
        forever begin
            @(posedge vif.clk);
            if(vif.start_cmd && !vif.busy) begin
                trans = pmu_seq_item::type_id::create("trans");
                trans.op_type      = vif.op_type;
                trans.power_domain = vif.power_domain;
                trans.voltage_level = vif.voltage_level;
                trans.frequency    = vif.frequency;
                trans.status       = vif.status;
                ap.write(trans);
            end
        end
    endtask
endclass

`endif
