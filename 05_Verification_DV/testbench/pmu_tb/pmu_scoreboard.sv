`ifndef PMU_SCOREBOARD_SV
`define PMU_SCOREBOARD_SV

class pmu_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(pmu_scoreboard)

    uvm_analysis_imp#(pmu_seq_item, pmu_scoreboard) item_collected_export;

    pmu_seq_item  trans_queue[$];
    int           match_count;
    int           mismatch_count;
    int           total_transactions;
    int           power_errors;
    int           protection_violations;

    function new(string name = "pmu_scoreboard", uvm_component parent = null);
        super.new(name, parent);
        item_collected_export = new("item_collected_export", this);
    endfunction

    virtual function void write(pmu_seq_item item);
        trans_queue.push_back(item);
        total_transactions++;
        check_transactions();
    endfunction

    virtual function void check_transactions();
        while(trans_queue.size() >= 2) begin
            pmu_seq_item req, rsp;
            trans_queue.pop_front(rsp);
            trans_queue.pop_front(req);

            if(compare_items(req, rsp)) begin
                match_count++;
            end else begin
                mismatch_count++;
                `uvm_error(get_name(), $sformatf("PMU MISMATCH: Operation %s", req.op_name))
            end

            if(rsp.status == PMU_ERR_POWER) begin
                power_errors++;
            end
            if(rsp.status == PMU_ERR_PROTECTION) begin
                protection_violations++;
            end
        end
    endfunction

    virtual function bit compare_items(pmu_seq_item req, pmu_seq_item rsp);
        if(req.op_type != rsp.op_type) return 0;
        if(req.power_domain != rsp.power_domain) return 0;
        return 1;
    endfunction

    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info(get_name(), $sformatf("PMU Scoreboard Report:"), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Total Transactions: %0d", total_transactions), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Matches: %0d", match_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Mismatches: %0d", mismatch_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Power Errors: %0d", power_errors), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Protection Violations: %0d", protection_violations), UVM_LOW)
    endfunction
endclass

`endif
