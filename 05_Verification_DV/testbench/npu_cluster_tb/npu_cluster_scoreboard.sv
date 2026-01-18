`ifndef NPU_CLUSTER_SCOREBOARD_SV
`define NPU_CLUSTER_SCOREBOARD_SV

class npu_cluster_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(npu_cluster_scoreboard)

    uvm_analysis_imp#(npu_cluster_seq_item, npu_cluster_scoreboard) item_collected_export;

    npu_cluster_seq_item  trans_queue[$];
    int                   match_count;
    int                   mismatch_count;
    int                   total_transactions;

    function new(string name = "npu_cluster_scoreboard", uvm_component parent = null);
        super.new(name, parent);
        item_collected_export = new("item_collected_export", this);
    endfunction

    virtual function void write(npu_cluster_seq_item item);
        trans_queue.push_back(item);
        total_transactions++;
        check_transactions();
    endfunction

    virtual function void check_transactions();
        while(trans_queue.size() >= 2) begin
            npu_cluster_seq_item req, rsp;
            trans_queue.pop_front(rsp);
            trans_queue.pop_front(req);

            if(compare_items(req, rsp)) begin
                match_count++;
                `uvm_info(get_name(), $sformatf("MATCH: Operation %s", req.op_name), UVM_DEBUG)
            end else begin
                mismatch_count++;
                `uvm_error(get_name(), $sformatf("MISMATCH: Operation %s", req.op_name))
                `uvm_info(get_name(), $sformatf("Request:\n%s", req.sprint()), UVM_LOW)
                `uvm_info(get_name(), $sformatf("Response:\n%s", rsp.sprint()), UVM_LOW)
            end
        end
    endfunction

    virtual function bit compare_items(npu_cluster_seq_item req, npu_cluster_seq_item rsp);
        if(req.op_type != rsp.op_type) return 0;
        if(req.status != rsp.status) return 0;
        return 1;
    endfunction

    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info(get_name(), $sformatf("Scoreboard Report:"), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Total Transactions: %0d", total_transactions), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Matches: %0d", match_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Mismatches: %0d", mismatch_count), UVM_LOW)
    endfunction
endclass

`endif
