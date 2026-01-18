`ifndef DV_CONFIG_SVH
`define DV_CONFIG_SVH

class dv_config extends uvm_object;
  bit enable_scoreboard = 1;
  bit enable_coverage = 1;
  bit enable_assertions = 1;

  int seed = 0;

  `uvm_object_utils_begin(dv_config)
    `uvm_field_int(enable_scoreboard, UVM_DEFAULT)
    `uvm_field_int(enable_coverage, UVM_DEFAULT)
    `uvm_field_int(enable_assertions, UVM_DEFAULT)
    `uvm_field_int(seed, UVM_DEFAULT)
  `uvm_object_utils_end

  function new(string name = "dv_config");
    super.new(name);
    if (seed == 0) seed = $random;
  endfunction

  static function dv_config get(uvm_component cntxt);
    dv_config cfg;
    if (!uvm_config_db#(dv_config)::get(cntxt, "", "dv_config", cfg)) begin
      cfg = new();
      uvm_config_db#(dv_config)::set(cntxt, "", "dv_config", cfg);
    end
    return cfg;
  endfunction
endclass

`endif
