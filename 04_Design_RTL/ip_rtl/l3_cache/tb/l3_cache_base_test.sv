// ============================================================================
// Test: l3_cache_base_test
// Description: L3 Cache Base Test
// Version: 1.0
// ============================================================================

`ifndef L3_CACHE_BASE_TEST_SV
`define L3_CACHE_BASE_TEST_SV

class l3_cache_base_test extends uvm_test;

    l3_cache_env                  env;
    l3_cache_config               cfg;

    `uvm_component_utils(l3_cache_base_test)

    function new(string name = "l3_cache_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // 创建配置
        cfg = l3_cache_config::type_id::create("cfg");
        cfg.is_active = 1;
        cfg.num_masters = 16;

        // 创建环境
        env = l3_cache_env::type_id::create("env", this);
    endfunction

    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        uvm_top.print_topology();
    endfunction

    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        #1us;
        phase.drop_objection(this);
    endtask

endclass

`endif
