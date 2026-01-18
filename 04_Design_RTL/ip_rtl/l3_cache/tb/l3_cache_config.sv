// ============================================================================
// Class: l3_cache_config
// Description: L3 Cache配置类
// Version: 1.0
// ============================================================================

`ifndef L3_CACHE_CONFIG_SV
`define L3_CACHE_CONFIG_SV

class l3_cache_config extends uvm_object;

    // 配置参数
    bit                         is_active = 1;
    int                         num_masters = 16;
    int                         cache_size = 8 * 1024 * 1024;
    int                         ways = 16;
    int                         line_size = 64;
    int                         data_width = 512;

    // 虚拟接口
    virtual l3_cache_intf       vif;

    `uvm_object_utils_begin(l3_cache_config)
        `uvm_field_int(is_active, UVM_DEFAULT)
        `uvm_field_int(num_masters, UVM_DEFAULT)
        `uvm_field_int(cache_size, UVM_DEFAULT)
        `uvm_field_int(ways, UVM_DEFAULT)
        `uvm_field_int(line_size, UVM_DEFAULT)
        `uvm_field_int(data_width, UVM_DEFAULT)
    `uvm_object_utils_end

    function new(string name = "l3_cache_config");
        super.new(name);
    endfunction

endclass

`endif
