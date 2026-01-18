// ============================================================================
// Test: l3_cache_regression_test
// Description: L3 Cache Regression Test
// Version: 1.0
// ============================================================================

`ifndef L3_CACHE_REGRESSION_TEST_SV
`define L3_CACHE_REGRESSION_TEST_SV

class l3_cache_regression_test extends l3_cache_base_test;

    `uvm_component_utils(l3_cache_regression_test)

    function new(string name = "l3_cache_regression_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);

        // 运行多个测试用例
        run_test("l3_cache_basic_test");
        run_test("l3_cache_burst_test");
        run_test("l3_cache_concurrent_test");
        run_test("l3_cache_stress_test");
        run_test("l3_cache_coverage_test");

        phase.drop_objection(this);
    endtask

endclass

`endif
