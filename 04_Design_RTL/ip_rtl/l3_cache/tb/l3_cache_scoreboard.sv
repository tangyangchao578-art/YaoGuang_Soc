// ============================================================================
// Class: l3_cache_scoreboard
// Description: L3 Cache Scoreboard
// Version: 1.0
// ============================================================================

`ifndef L3_CACHE_SCOREBOARD_SV
`define L3_CACHE_SCOREBOARD_SV

class l3_cache_scoreboard extends uvm_scoreboard;

    uvm_analysis_export#(l3_cache_seq_item) expected_export;
    uvm_analysis_export#(l3_cache_seq_item) actual_export;

    l3_cache_seq_item                 expected_q[$];
    l3_cache_seq_item                 actual_q[$];

    int                               passed = 0;
    int                               failed = 0;

    `uvm_component_utils(l3_cache_scoreboard)

    function new(string name = "l3_cache_scoreboard", uvm_component parent = null);
        super.new(name, parent);
        expected_export = new("expected_export", this);
        actual_export = new("actual_export", this);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
    endfunction

    virtual task run_phase(uvm_phase phase);
        fork
            process_expected();
            process_actual();
        join
    endtask

    virtual task process_expected();
        forever begin
            l3_cache_seq_item item;
            expected_export.get(item);
            expected_q.push_back(item);
        end
    endtask

    virtual task process_actual();
        forever begin
            l3_cache_seq_item item;
            actual_export.get(item);
            actual_q.push_back(item);
            compare_results();
        end
    endtask

    virtual function void compare_results();
        if (expected_q.size() > 0 && actual_q.size() > 0) begin
            l3_cache_exp = expected_q.pop_front();
            l3_cache_act = actual_q.pop_front();

            if (l3_cache_exp.compare(l3_cache_act)) begin
                passed++;
                `uvm_info("SCOREBOARD", "Transaction PASSED", UVM_LOW)
            end else begin
                failed++;
                `uvm_error("SCOREBOARD", $sformatf("Transaction FAILED: expected=%s actual=%s",
                                                    l3_cache_exp.convert2string(),
                                                    l3_cache_act.convert2string()))
            end
        end
    endfunction

    virtual function void report_phase(uvm_phase phase);
        `uvm_info("SCOREBOARD", $sformatf("Scoreboard Report: passed=%0d failed=%0d", passed, failed), UVM_LOW)
    endfunction

endclass

`endif
