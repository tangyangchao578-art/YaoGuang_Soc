//-----------------------------------------------------------------------------
// File: cpu_coverage.sv
// Description: CPU Subsystem coverage monitor
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef CPU_COVERAGE_SV
`define CPU_COVERAGE_SV

class cpu_coverage extends uvm_component;
    `uvm_component_utils(cpu_coverage)

    cpu_config cfg;
    virtual cpu_if vif;

    covergroup cpu_inst_cg with function sample(cpu_transaction tr);
        option.per_instance = 1;

        cp_opcode: coverpoint tr.opcode {
            bins OP_LOAD = {OP_LOAD};
            bins OP_STORE = {OP_STORE};
            bins OP_BRANCH = {OP_BRANCH};
            bins OP_ALU = {OP_ALU};
            bins OP_FPU = {OP_FPU};
            bins OP_SIMD = {OP_SIMD};
            bins OP_SYSTEM = {OP_SYSTEM};
        }

        cp_privilege: coverpoint tr.privilege {
            bins PRIV_KERNEL = {PRIV_KERNEL};
            bins PRIV_USER = {PRIV_USER};
            bins PRIV_HYPERVISOR = {PRIV_HYPERVISOR};
        }

        cp_exception: coverpoint tr.has_exception {
            bins EXC_NONE = {0};
            bins EXC_IRQ = {1};
            bins EXC_FIQ = {2};
            bins EXC_DATA_ABORT = {3};
            bins EXC_PREFETCH_ABORT = {4};
            bins EXC_SVC = {5};
        }
    endgroup

    covergroup cpu_cache_cg with function sample(cpu_transaction tr);
        option.per_instance = 1;

        cp_cache_op: coverpoint tr.cache_op {
            bins CACHE_NONE = {CACHE_NONE};
            bins CACHE_CLEAN = {CACHE_CLEAN};
            bins CACHE_INVALIDATE = {CACHE_INVALIDATE};
            bins CACHE_FLUSH = {CACHE_FLUSH};
        }

        cp_cache_level: coverpoint tr.cache_level {
            bins LEVEL_L1 = {0};
            bins LEVEL_L2 = {1};
        }

        cp_mmu_state: coverpoint tr.mmu_state {
            bins MMU_DISABLED = {0};
            bins MMU_ENABLED = {1};
        }
    endgroup

    covergroup cpu_gic_cg with function sample(cpu_transaction tr);
        option.per_instance = 1;

        cp_irq_type: coverpoint tr.irq_type {
            bins IRQ_SGI = {0};
            bins IRQ_PPI = {1};
            bins IRQ_SPI = {2};
        }

        cp_irq_prio: coverpoint tr.irq_prio {
            bins PRIO_HIGH = {[0:63]};
            bins PRIO_MED = {[64:127]};
            bins PRIO_LOW = {[128:255]};
        }

        cp_irq_enable: coverpoint tr.irq_enabled {
            bins ENABLED = {1};
            bins DISABLED = {0};
        }
    endgroup

    covergroup cpu_pipeline_cg with function sample(cpu_transaction tr);
        option.per_instance = 1;

        cp_stall: coverpoint tr.stall_reason {
            bins STALL_NONE = {STALL_NONE};
            bins STALL_CACHE_MISS = {STALL_CACHE_MISS};
            bins STALL_TLB_MISS = {STALL_TLB_MISS};
            bins STALL_DEPENDENCY = {STALL_DEPENDENCY};
            bins STALL_RESOURCE = {STALL_RESOURCE};
        }

        cp_bpred: coverpoint tr.branch_predicted {
            bins BP_TAKEN = {1};
            bins BP_NOT_TAKEN = {0};
        }
    endgroup

    function new(string name, uvm_component parent);
        super.new(name, parent);
        cpu_inst_cg = new();
        cpu_cache_cg = new();
        cpu_gic_cg = new();
        cpu_pipeline_cg = new();
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual cpu_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("CPU_COVERAGE", "Virtual interface not found")
        end
        cfg = cpu_config::type_id::create("cfg", this);
    endfunction

    virtual task run_phase(uvm_phase phase);
        cpu_transaction tr;
        forever begin
            @(posedge vif.clk);
            if(vif.valid && cfg.enable_coverage) begin
                tr = new();
                tr.opcode = vif.opcode;
                tr.privilege = vif.privilege;
                tr.cache_op = vif.cache_op;
                tr.irq_type = vif.irq_type;
                sample_transaction(tr);
            end
        end
    endtask

    virtual function void sample_transaction(cpu_transaction tr);
        if(cfg.cov_cache_enable) cpu_cache_cg.sample(tr);
        if(cfg.cov_mmu_enable) cpu_inst_cg.sample(tr);
        if(cfg.cov_gic_enable) cpu_gic_cg.sample(tr);
        if(cfg.cov_pipeline_enable) cpu_pipeline_cg.sample(tr);
    endfunction

    virtual function void report_phase(uvm_phase phase);
        real cov_inst, cov_cache, cov_gic, cov_pipeline;

        cov_inst = cpu_inst_cg.get_coverage();
        cov_cache = cpu_cache_cg.get_coverage();
        cov_gic = cpu_gic_cg.get_coverage();
        cov_pipeline = cpu_pipeline_cg.get_coverage();

        `uvm_info("CPU_COVERAGE", $sformatf("=== Coverage Report ==="), UVM_LOW)
        `uvm_info("CPU_COVERAGE", $sformatf("Instruction Coverage: %0.1f%%", cov_inst), UVM_LOW)
        `uvm_info("CPU_COVERAGE", $sformatf("Cache Coverage: %0.1f%%", cov_cache), UVM_LOW)
        `uvm_info("CPU_COVERAGE", $sformatf("GIC Coverage: %0.1f%%", cov_gic), UVM_LOW)
        `uvm_info("CPU_COVERAGE", $sformatf("Pipeline Coverage: %0.1f%%", cov_pipeline), UVM_LOW)
    endfunction
endclass

`endif
