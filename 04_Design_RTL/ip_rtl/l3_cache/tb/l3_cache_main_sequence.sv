// ============================================================================
// Class: l3_cache_main_sequence
// Description: L3 Cache Main Test Sequence
// Version: 1.0
// ============================================================================

`ifndef L3_CACHE_MAIN_SEQUENCE_SV
`define L3_CACHE_MAIN_SEQUENCE_SV

class l3_cache_main_sequence extends l3_cache_base_sequence;

    int                             num_transactions = 1000;
    int                             num_masters = 16;

    `uvm_object_utils(l3_cache_main_sequence)

    function new(string name = "l3_cache_main_sequence");
        super.new(name);
    endtask

    virtual task body();
        for (int i = 0; i < num_transactions; i++) begin
            l3_cache_seq_item item = l3_cache_seq_item::type_id::create("item");
            start_item(item);
            if (!randomize(item) with {
                is_read dist {1 := 60, 0 := 40};
                master_id inside {[0:num_masters-1]};
                addr[31:20] == 0;  // Cacheable地址
            }) begin
                `uvm_error("RAND", "Randomization failed")
            end
            finish_item(item);
        end
    endtask

endclass

`endif
