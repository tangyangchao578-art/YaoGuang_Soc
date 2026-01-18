//-----------------------------------------------------------------------------
// Safety Island Scoreboard
// YaoGuang SoC ASIL-D Safety Module Verification
//-----------------------------------------------------------------------------
`ifndef SAFETY_ISLAND_SCOREBOARD_SV
`define SAFETY_ISLAND_SCOREBOARD_SV

class safety_island_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(safety_island_scoreboard)
    
    uvm_tlm_analysis_fifo#(safety_island_transaction) agent_export;
    safety_island_transaction  expected_queue[$];
    safety_island_transaction  actual_queue[$];
    
    int                         mismatch_count = 0;
    int                         match_count = 0;
    
    function new(string name = "safety_island_scoreboard", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        agent_export = new("agent_export", this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        safety_island_transaction tr;
        forever begin
            agent_export.get(tr);
            process_transaction(tr);
        end
    endtask
    
    virtual protected function void process_transaction(safety_island_transaction tr);
        if(tr.opcode == SI_OP_NOP) begin
            expected_queue.push_back(tr);
        end else begin
            if(expected_queue.size() > 0) begin
                safety_island_transaction exp = expected_queue.pop_front();
                if(compare_transactions(exp, tr)) begin
                    match_count++;
                    `uvm_info("SCO", $sformatf("Match: %s", tr.convert2string()), UVM_LOW)
                end else begin
                    mismatch_count++;
                    `uvm_error("SCO", $sformatf("Mismatch: expected=%s actual=%s", 
                        exp.convert2string(), tr.convert2string()))
                end
            end
        end
    endfunction
    
    virtual protected function bit compare_transactions(safety_island_transaction exp, 
                                                         safety_island_transaction act);
        return (exp.opcode == act.opcode) && (exp.addr == act.addr) && (exp.data == act.data);
    endfunction
    
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("SCO", $sformatf("Scoreboard Report: Match=%0d Mismatch=%0d", 
            match_count, mismatch_count), UVM_LOW)
        if(mismatch_count > 0) begin
            `uvm_error("SCO", "Scoreboard found mismatches!")
        end
    endfunction
endclass

`endif
