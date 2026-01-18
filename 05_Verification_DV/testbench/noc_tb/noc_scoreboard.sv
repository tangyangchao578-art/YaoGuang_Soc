`ifndef NOC_SCOREBOARD_SV
`define NOC_SCOREBOARD_SV

class noc_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(noc_scoreboard)

    uvm_analysis_imp#(noc_seq_item, noc_scoreboard) item_collected_export;

    noc_seq_item  trans_queue[$];
    int           match_count;
    int           mismatch_count;
    int           total_packets;
    int           deadlocks;
    int           timeouts;

    function new(string name = "noc_scoreboard", uvm_component parent = null);
        super.new(name, parent);
        item_collected_export = new("item_collected_export", this);
    endfunction

    virtual function void write(noc_seq_item item);
        trans_queue.push_back(item);
        total_packets++;
        check_transactions();
    endfunction

    virtual function void check_transactions();
        while(trans_queue.size() >= 2) begin
            noc_seq_item req, rsp;
            trans_queue.pop_front(rsp);
            trans_queue.pop_front(req);

            if(compare_items(req, rsp)) begin
                match_count++;
            end else begin
                mismatch_count++;
                `uvm_error(get_name(), $sformatf("NoC MISMATCH: src=%0d dst=%0d", req.src_id, req.dst_id))
            end

            if(rsp.status == NOC_ERR_TIMEOUT) begin
                timeouts++;
            end
            if(rsp.status == NOC_ERR_DEADLOCK) begin
                deadlocks++;
            end
        end
    endfunction

    virtual function bit compare_items(noc_seq_item req, noc_seq_item rsp);
        if(req.packet_id != rsp.packet_id) return 0;
        if(req.src_id != rsp.src_id) return 0;
        if(req.dst_id != rsp.dst_id) return 0;
        return 1;
    endfunction

    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info(get_name(), $sformatf("NoC Scoreboard Report:"), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Total Packets: %0d", total_packets), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Matches: %0d", match_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Mismatches: %0d", mismatch_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Timeouts: %0d", timeouts), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Deadlocks: %0d", deadlocks), UVM_LOW)
    endfunction
endclass

`endif
