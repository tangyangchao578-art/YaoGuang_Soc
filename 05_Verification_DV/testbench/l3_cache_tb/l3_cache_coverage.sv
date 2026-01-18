//-----------------------------------------------------------------------------
// File: l3_cache_coverage.sv
// Description: L3 Cache coverage monitor
// Author: YaoGuang SoC DV Team
// Date: 2026-01-18
//-----------------------------------------------------------------------------
`ifndef L3_CACHE_COVERAGE_SV
`define L3_CACHE_COVERAGE_SV

class l3_cache_coverage extends uvm_component;
    `uvm_component_utils(l3_cache_coverage)

    l3_cache_config cfg;
    virtual l3_cache_if vif;

    covergroup l3_access_cg with function sample(l3_cache_transaction tr);
        option.per_instance = 1;

        cp_op: coverpoint tr.op {
            bins OP_READ = {L3_OP_READ};
            bins OP_WRITE = {L3_OP_WRITE};
            bins OP_CLEAN = {L3_OP_CLEAN};
            bins OP_INVALIDATE = {L3_OP_INVALIDATE};
            bins OP_EVICT = {L3_OP_EVICT};
            bins OP_SNOOP = {L3_OP_SNOOP};
        }

        cp_response: coverpoint tr.response {
            bins RESP_HIT = {L3_RESP_HIT};
            bins RESP_MISS = {L3_RESP_MISS};
            bins RESP_STALL = {L3_RESP_STALL};
        }

        cp_bank: coverpoint tr.id[3:0] {
            bins BANK0 = {[0:3]};
            bins BANK1 = {[4:7]};
            bins BANK2 = {[8:11]};
            bins BANK3 = {[12:15]};
        }
    endgroup

    covergroup l3_tag_cg with function sample(l3_cache_transaction tr);
        option.per_instance = 1;

        cp_tag_bits: coverpoint tr.tag[7:0] {
            bins LOW = {[0:63]};
            bins MID = {[64:127]};
            bins HIGH = {[128:255]};
        }

        cp_index_bits: coverpoint tr.index {
            bins LOW_INDEX = {[0:255]};
            bins MID_INDEX = {[256:511]};
            bins HIGH_INDEX = {[512:1023]};
        }

        cp_way: coverpoint tr.way {
            bins WAY0 = {0};
            bins WAY1 = {1};
            bins WAY2 = {2};
            bins WAY3 = {3};
        }
    endgroup

    covergroup l3_perf_cg with function sample(l3_cache_transaction tr);
        option.per_instance = 1;

        cp_latency: coverpoint tr.response {
            bins LATENCY_LOW = {L3_RESP_HIT};
            bins LATENCY_MED = {L3_RESP_MISS};
            bins LATENCY_HIGH = {L3_RESP_STALL};
        }

        cp_priority: coverpoint tr.priority {
            bins PRIO_HIGH = {[0:63]};
            bins PRIO_LOW = {[64:255]};
        }
    endgroup

    covergroup l3_snoop_cg with function sample(l3_cache_transaction tr);
        option.per_instance = 1;

        cp_snoop_valid: coverpoint tr.valid {
            bins VALID = {1};
            bins INVALID = {0};
        }

        cp_snoop_response: coverpoint tr.response {
            bins SNOP_HIT = {L3_RESP_HIT};
            bins SNOP_MISS = {L3_RESP_MISS};
        }
    endgroup

    function new(string name, uvm_component parent);
        super.new(name, parent);
        l3_access_cg = new();
        l3_tag_cg = new();
        l3_perf_cg = new();
        l3_snoop_cg = new();
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual l3_cache_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("L3_CACHE_COVERAGE", "Virtual interface not found")
        end
        cfg = l3_cache_config::type_id::create("cfg", this);
    endfunction

    virtual task run_phase(uvm_phase phase);
        l3_cache_transaction tr;
        forever begin
            @(posedge vif.clk);
            if(vif.valid && cfg.enable_coverage) begin
                tr = new();
                tr.op = vif.op;
                tr.response = vif.response;
                tr.id = vif.id;
                tr.priority = vif.priority;
                tr.valid = vif.valid;
                sample_transaction(tr);
            end
        end
    endtask

    virtual function void sample_transaction(l3_cache_transaction tr);
        l3_access_cg.sample(tr);
        l3_perf_cg.sample(tr);
        l3_snoop_cg.sample(tr);
    endfunction

    virtual function void report_phase(uvm_phase phase);
        real cov_access, cov_tag, cov_perf, cov_snoop;

        cov_access = l3_access_cg.get_coverage();
        cov_tag = l3_tag_cg.get_coverage();
        cov_perf = l3_perf_cg.get_coverage();
        cov_snoop = l3_snoop_cg.get_coverage();

        `uvm_info("L3_CACHE_COVERAGE", $sformatf("=== L3 Cache Coverage Report ==="), UVM_LOW)
        `uvm_info("L3_CACHE_COVERAGE", $sformatf("Access Coverage: %0.1f%%", cov_access), UVM_LOW)
        `uvm_info("L3_CACHE_COVERAGE", $sformatf("Tag Coverage: %0.1f%%", cov_tag), UVM_LOW)
        `uvm_info("L3_CACHE_COVERAGE", $sformatf("Performance Coverage: %0.1f%%", cov_perf), UVM_LOW)
        `uvm_info("L3_CACHE_COVERAGE", $sformatf("Snoop Coverage: %0.1f%%", cov_snoop), UVM_LOW)
    endfunction
endclass

`endif
