// ============================================================================
// Class: l3_cache_reference_model
// Description: L3 Cache Reference Model
// Version: 1.0
// ============================================================================

`ifndef L3_CACHE_REFERENCE_MODEL_SV
`define L3_CACHE_REFERENCE_MODEL_SV

class l3_cache_reference_model extends uvm_component;

    uvm_analysis_port#(l3_cache_seq_item) ap;
    import "DPI-C" context task ref_model_task(
        input int is_read,
        input int addr,
        input int len,
        input int master_id,
        output int resp
    );

    `uvm_component_utils(l3_cache_reference_model)

    function new(string name = "l3_cache_reference_model", uvm_component parent = null);
        super.new(name, parent);
        ap = new("ap", this);
    endfunction

    virtual task run_phase(uvm_phase phase);
        // 调用C++参考模型
    endtask

endclass

`endif
