#===========================================
# CPU Cluster File List
#===========================================
# YaoGuang SoC - CPU Cluster RTL
# Version: 1.0
# Date: 2026-01-19
#===========================================

# Top-level
+incdir+.
04_Design_RTL/ip_rtl/cpu_cluster/cpu_cluster_top.sv

# A78AE Cluster
04_Design_RTL/ip_rtl/cpu_cluster/cortex_a78ae_core_x8.sv

# R52 Lockstep Cluster
04_Design_RTL/ip_rtl/cpu_cluster/cortex_r52_lockstep.sv

# L2 Cache
04_Design_RTL/ip_rtl/cpu_cluster/l2_cache_a78ae.sv

# Snoop Control Unit
04_Design_RTL/ip_rtl/cpu_cluster/snoop_control_unit.sv

# Interrupt Controller (GIC-600)
04_Design_RTL/ip_rtl/cpu_cluster/interrupt_controller.sv

# Interconnects
04_Design_RTL/ip_rtl/cpu_cluster/ace_interconnect_8to1.sv
04_Design_RTL/ip_rtl/cpu_cluster/axi_interconnect_2to1.sv

# Constraints
04_Design_RTL/ip_rtl/cpu_cluster/cpu_cluster.sdc

# Documentation
04_Design_RTL/ip_rtl/cpu_cluster/FEATURE_LIST.md
