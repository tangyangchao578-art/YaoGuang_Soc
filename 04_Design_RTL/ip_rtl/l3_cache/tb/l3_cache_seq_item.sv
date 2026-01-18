// ============================================================================
// Class: l3_cache_sequence_item
// Description: L3 Cache事务项
// Version: 1.0
// ============================================================================

`ifndef L3_CACHE_SEQUENCE_ITEM_SV
`define L3_CACHE_SEQUENCE_ITEM_SV

class l3_cache_seq_item extends uvm_sequence_item;

    // 事务类型
    rand bit                    is_read;
    rand bit [31:0]             addr;
    rand bit [7:0]              len;
    rand bit [2:0]              size;
    rand bit [DATA_WIDTH-1:0]   data;
    rand bit [63:0]             strb;
    rand int                    master_id;

    // 响应
    bit [1:0]                   resp;
    bit [DATA_WIDTH-1:0]        rdata;
    bit                         rlast;

    // 延迟
    rand int                    delay;

    `uvm_object_utils_begin(l3_cache_seq_item)
        `uvm_field_int(is_read, UVM_DEFAULT)
        `uvm_field_int(addr, UVM_DEFAULT)
        `uvm_field_int(len, UVM_DEFAULT)
        `uvm_field_int(size, UVM_DEFAULT)
        `uvm_field_int(data, UVM_DEFAULT)
        `uvm_field_int(strb, UVM_DEFAULT)
        `uvm_field_int(master_id, UVM_DEFAULT)
        `uvm_field_int(resp, UVM_DEFAULT)
        `uvm_field_int(rdata, UVM_DEFAULT)
        `uvm_field_int(rlast, UVM_DEFAULT)
        `uvm_field_int(delay, UVM_DEFAULT)
    `uvm_object_utils_end

    constraint default_size {
        size dist {3 := 50, 6 := 50};  // 8B or 64B
    }

    constraint default_len {
        len dist {0 := 20, 7 := 40, 15 := 40};
    }

    constraint default_delay {
        delay inside {[1:10]};
    }

    function new(string name = "l3_cache_seq_item");
        super.new(name);
    endfunction

    function string convert2string();
        return $sformatf("is_read=%0b addr=0x%08h len=%0d master=%0d",
                         is_read, addr, len, master_id);
    endfunction

endclass

`endif
