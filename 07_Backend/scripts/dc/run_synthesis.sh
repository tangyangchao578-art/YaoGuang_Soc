#!/bin/bash
#===============================================================================
# YaoGuang SoC Synthesis Shell Wrapper Script
# Version: V1.0
# Date: 2026-01-18
#===============================================================================

#===============================================================================
# 1. 环境设置
#===============================================================================

# 设置Synthesis主目录
export SYNTH_HOME="$(cd "$(dirname "$0")" && pwd)"

# 设置Design Compiler路径
export DC_HOME=${DC_HOME:-/opt/synopsys/syn/2023.03}
export PATH=$DC_HOME/bin:$PATH

# 设置许可证
export SNPSLMD_LICENSE_FILE=27000@synopsys-license-server

# 设置临时目录
export TMPDIR=/tmp/yaoguang_synth_$$
mkdir -p $TMPDIR

#===============================================================================
# 2. 打印启动信息
#===============================================================================
echo "========================================"
echo "  YaoGuang SoC Logic Synthesis"
echo "========================================"
echo "Date:         $(date)"
echo "Synthesis Home: $SYNTH_HOME"
echo "DC Version:    $($DC_HOME/bin/dc_shell -version 2>/dev/null | head -1)"
echo "Target:       TSMC 5nm"
echo "Frequency:    2.0 GHz (Core/NPU), 500 MHz (System)"
echo ""

#===============================================================================
# 3. 检查环境
#===============================================================================
echo "Checking environment..."

# 检查DC_HOME
if [ ! -d "$DC_HOME" ]; then
    echo "ERROR: Design Compiler not found at $DC_HOME"
    exit 1
fi

# 检查RTL目录
RTL_DIR="$SYNTH_HOME/../04_Design_RTL"
if [ ! -d "$RTL_DIR" ]; then
    echo "ERROR: RTL directory not found: $RTL_DIR"
    exit 1
fi

# 检查SDC文件
SDC_FILE="$SYNTH_HOME/../sdc/yaoguang_soc.sdc"
if [ ! -f "$SDC_FILE" ]; then
    echo "ERROR: SDC file not found: $SDC_FILE"
    exit 1
fi

echo "Environment check passed"
echo ""

#===============================================================================
# 4. 清理输出目录
#===============================================================================
OUTPUT_DIR="$SYNTH_HOME/../output"
REPORT_DIR="$SYNTH_HOME/../reports"

echo "Cleaning output directories..."
rm -rf $OUTPUT_DIR/*
rm -rf $REPORT_DIR/*
mkdir -p $OUTPUT_DIR
mkdir -p $REPORT_DIR

echo "Output directories ready"
echo ""

#===============================================================================
# 5. 执行综合
#===============================================================================
echo "========================================"
echo "  Starting Synthesis"
echo "========================================"

# 记录开始时间
START_TIME=$(date +%s)

# 进入脚本目录
cd $SYNTH_HOME/scripts/dc

# 执行DC综合 (使用dc_shell)
echo "Running Design Compiler..."
dc_shell -f dc_synthesis.tcl -output_log_file $OUTPUT_DIR/synthesis.log

# 检查综合结果
SYNTH_EXIT_CODE=$?

# 记录结束时间
END_TIME=$(date +%s)
DURATION=$((END_TIME - START_TIME))

echo ""
echo "========================================"
echo "  Synthesis Complete"
echo "========================================"
echo "Duration: ${DURATION} seconds"
echo "Exit Code: $SYNTH_EXIT_CODE"

#===============================================================================
# 6. 检查输出文件
#===============================================================================
echo ""
echo "========================================"
echo "  Output Files"
echo "========================================"

NETLIST_FILE="$OUTPUT_DIR/yaoguang_soc_netlist.v"
SDC_FILE_OUT="$OUTPUT_DIR/yaoguang_soc_sdc.out.sdc"
AREA_REPORT="$REPORT_DIR/area.rpt"
TIMING_REPORT="$REPORT_DIR/timing.rpt"
POWER_REPORT="$REPORT_DIR/power.rpt"

echo "Netlist:      $([ -f "$NETLIST_FILE" ] && echo "OK" || echo "MISSING") - $NETLIST_FILE"
echo "SDC:          $([ -f "$SDC_FILE_OUT" ] && echo "OK" || echo "MISSING") - $SDC_FILE_OUT"
echo "Area Report:  $([ -f "$AREA_REPORT" ] && echo "OK" || echo "MISSING") - $AREA_REPORT"
echo "Timing Report: $([ -f "$TIMING_REPORT" ] && echo "OK" || echo "MISSING") - $TIMING_REPORT"
echo "Power Report:  $([ -f "$POWER_REPORT" ] && echo "OK" || echo "MISSING") - $POWER_REPORT"

#===============================================================================
# 7. 提取关键指标
#===============================================================================
echo ""
echo "========================================"
echo "  Key Metrics"
echo "========================================"

# 提取面积信息
if [ -f "$AREA_REPORT" ]; then
    echo ""
    echo "Area Summary:"
    grep -A 5 "Total cell area" "$AREA_REPORT" 2>/dev/null || echo "  Area info not available"
    grep "Number of cells" "$AREA_REPORT" 2>/dev/null || echo "  Cell count not available"
    grep "Number of registers" "$AREA_REPORT" 2>/dev/null || echo "  Register count not available"
fi

# 提取时序信息
if [ -f "$TIMING_REPORT" ]; then
    echo ""
    echo "Timing Summary:"
    grep -E "(slack|WNS|TNS)" "$TIMING_REPORT" 2>/dev/null | head -10 || echo "  Timing info not available"
fi

# 提取功耗信息
if [ -f "$POWER_REPORT" ]; then
    echo ""
    echo "Power Summary:"
    grep -E "(Total Dynamic|Leakage|Total)" "$POWER_REPORT" 2>/dev/null | head -10 || echo "  Power info not available"
fi

#===============================================================================
# 8. 清理临时文件
#===============================================================================
echo ""
echo "Cleaning up temporary files..."
rm -rf $TMPDIR

#===============================================================================
# 9. 完成
#===============================================================================
echo ""
echo "========================================"
echo "  Synthesis Finished"
echo "========================================"
echo "Log file: $OUTPUT_DIR/synthesis.log"
echo ""

# 退出
exit $SYNTH_EXIT_CODE
