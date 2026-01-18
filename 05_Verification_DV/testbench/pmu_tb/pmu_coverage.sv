`ifndef PMU_COVERAGE_SV
`define PMU_COVERAGE_SV

class pmu_coverage extends uvm_subscriber#(pmu_seq_item);
    `uvm_component_utils(pmu_coverage)

    pmu_seq_item  trans;

    covergroup pmu_cg;
        option.per_instance = 1;
        op_type: coverpoint trans.op_type {
            bins POWER_ON     = {PMU_POWER_ON};
            bins POWER_OFF    = {PMU_POWER_OFF};
            bins DVFS_SET     = {PMU_DVFS_SET};
            bins LOW_POWER    = {PMU_LOW_POWER};
            bins SLEEP        = {PMU_SLEEP};
            bins WAKEUP       = {PMU_WAKEUP};
            bins PROTECT      = {PMU_PROTECT};
        }
        power_domain: coverpoint trans.power_domain {
            bins PD_CPU     = {0};
            bins PD_GPU     = {1};
            bins PD_NPU     = {2};
            bins PD_MEM     = {3};
            bins PD_PERI    = {4};
        }
        voltage_level: coverpoint trans.voltage_level {
            bins V_0V9   = {0};
            bins V_1V0   = {1};
            bins V_1V1   = {2};
            bins V_1V2   = {3};
        }
        frequency: coverpoint trans.frequency {
            bins F_500M  = {500};
            bins F_1G    = {1000};
            bins F_1_5G  = {1500};
            bins F_2G    = {2000};
        }
        status: coverpoint trans.status {
            bins SUCCESS = {0};
            bins ERR_POWER = {PMU_ERR_POWER};
            bins ERR_PROTECT = {PMU_ERR_PROTECTION};
            bins ERR_TIMEOUT = {PMU_ERR_TIMEOUT};
        }
        cross_op_domain: cross op_type, power_domain;
        cross_dvfs: cross op_type, voltage_level, frequency;
    endgroup

    function new(string name = "pmu_coverage", uvm_component parent = null);
        super.new(name, parent);
        pmu_cg = new();
    endfunction

    virtual function void write(T t);
        trans = t;
        pmu_cg.sample();
    endfunction

    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info(get_name(), $sformatf("PMU Coverage Report:"), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Overall Coverage: %0.2f%%", pmu_cg.get_inst_coverage()), UVM_LOW)
    endfunction
endclass

`endif
