#!/bin/bash
# YaoGuang SoC Physical Verification Script

cd /path/to/calibre

# 运行DRC
echo "Running DRC..."
calibre -drc -hier -turbo -64 yaoguang_drc.runset

# 检查DRC结果
if [ -f yaoguang_drc.results ]; then
    echo "DRC completed. Checking results..."
    grep -c "DRC VIOLATIONS" yaoguang_drc.results || echo "No DRC violations found"
fi

# 运行LVS
echo "Running LVS..."
calibre -lvs -hier yaoguang_lvs.runset

# 检查LVS结果
if [ -f yaoguang_lvs.results ]; then
    echo "LVS completed. Checking results..."
    tail -20 yaoguang_lvs.report
fi

# 运行Antenna
echo "Running Antenna Check..."
calibre -antenna yaoguang_antenna.runset
