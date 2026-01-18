// ============================================================================
// File: l3_cache.f
// Description: L3 Cache文件列表
// Version: 1.0
// ============================================================================

// 定义文件
+incdir+./rtl
./rtl/l3_cache_define.svh

// 顶层模块
./rtl/l3_cache_top.sv

// 子模块
./rtl/l3_tag_array.sv
./rtl/l3_data_array.sv
./rtl/l3_mshr.sv
./rtl/l3_plru.sv
./rtl/l3_request_handler.sv
