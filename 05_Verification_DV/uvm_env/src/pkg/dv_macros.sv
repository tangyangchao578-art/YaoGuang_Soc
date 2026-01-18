`ifndef DV_MACROS_SVH
`define DV_MACROS_SVH

`define DV_INFO(MSG) \
  `uvm_info(get_type_name(), MSG, UVM_MEDIUM)

`define DV_ERROR(MSG) \
  `uvm_error(get_type_name(), MSG)

`define DV_WARNING(MSG) \
  `uvm_warning(get_type_name(), MSG)

`define DV_CHECK(EXP, MSG) \
  if (!(EXP)) begin \
    `uvm_error(get_type_name(), $sformatf("DV_CHECK failed: %s", MSG)) \
  end

`define DV_ASSERT(SIGNAL, MSG) \
  `uvm_assert_create({"assertion_", get_type_name()}, SIGNAL, MSG)

`define DV_COVER_POINT(NAME) \
  covergroup NAME with function sample(bit [31:0] data); \
    option.per_instance = 1; \
  endgroup

`endif
