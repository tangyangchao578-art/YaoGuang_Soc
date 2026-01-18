# YaoGuang SoC UVM Verification File List
# Generated: 2026-01-18

# UVM Package
+incdir+${UVM_HOME}/src
${UVM_HOME}/src/uvm.sv

# Common DV Package
+incdir+../src/pkg
../src/pkg/dv_pkg.sv
../src/pkg/dv_macros.sv

# UVM Components
+incdir+../src/component
../src/component/dv_config.sv
../src/component/dv_sequence_item.sv
../src/component/dv_sequence.sv
../src/component/dv_driver.sv
../src/component/dv_monitor.sv
../src/component/dv_sequencer.sv
../src/component/dv_agent.sv
../src/component/dv_scoreboard.sv
../src/component/dv_coverage.sv
../src/component/dv_env.sv

# AXI4 VIP
+incdir+../vip
../vip/axi4_vip.sv

# APB4 VIP
../vip/apb4_vip.sv

# Assertions
../src/component/axi4_assertions.sv
../src/component/axi4_sb.sv

# Testbench Top
../tb/top_tb.sv

# Test Cases
../tests/dv_base_test.sv
../tests/pmu_tests.sv
../tests/safety_tests.sv
../tests/noc_tests.sv

# RTL DUT
+incdir+../../04_Design_RTL
../../04_Design_RTL/ip_rtl/pmu/rtl/pmu_top.sv
../../04_Design_RTL/ip_rtl/safety_island/rtl/safety_island_top.sv
../../04_Design_RTL/ip_rtl/noc/rtl/noc_top.sv
