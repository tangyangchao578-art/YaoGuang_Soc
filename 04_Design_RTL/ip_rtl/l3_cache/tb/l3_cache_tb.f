// ============================================================================
// File: l3_cache_tb.f
// Description: L3 Cache Testbench文件列表
// Version: 1.0
// ============================================================================

// 接口定义
+incdir+./tb
./tb/l3_cache_intf.sv

// 配置和序列项
./tb/l3_cache_config.sv
./tb/l3_cache_seq_item.sv

// Agent组件
./tb/l3_cache_driver.sv
./tb/l3_cache_monitor.sv
./tb/l3_cache_sequencer.sv
./tb/l3_cache_agent.sv

// Scoreboard和参考模型
./tb/l3_cache_scoreboard.sv
./tb/l3_cache_reference_model.sv
./tb/l3_cache_coverage.sv

// Sequencer
./tb/l3_cache_virtual_sequencer.sv
./tb/l3_cache_base_sequence.sv
./tb/l3_cache_main_sequence.sv

// 环境
./tb/l3_cache_env.sv

// 测试
./tb/l3_cache_base_test.sv
./tb/l3_cache_regression_test.sv
