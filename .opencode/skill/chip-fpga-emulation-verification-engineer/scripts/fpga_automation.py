#!/usr/bin/env python3
"""
FPGA原型验证自动化脚本
提供编译、下载、测试和报告生成功能
"""

import subprocess
import argparse
import sys
import os
import json
import time
from datetime import datetime

class FPGAValidator:
    def __init__(self, config_file="fpga_config.json"):
        self.config = self.load_config(config_file)
        self.results = []
        
    def load_config(self, config_file):
        """加载配置文件"""
        try:
            with open(config_file, 'r') as f:
                return json.load(f)
        except FileNotFoundError:
            print(f"Warning: Config file {config_file} not found, using defaults")
            return {
                "project": {
                    "name": "fpga_project",
                    "top": "top",
                    "part": "xc7k325tffg900-2",
                    "rtl_dir": "rtl",
                    "constraint_file": "constraints.xdc"
                },
                "tests": {
                    "dir": "tests",
                    "timeout": 300
                },
                "reports": {
                    "dir": "reports"
                }
            }
    
    def compile_fpga(self):
        """编译FPGA设计"""
        print("Starting FPGA compilation...")
        
        # 创建Vivado TCL脚本
        tcl_script = self.generate_compile_script()
        
        # 运行Vivado
        try:
            cmd = ["vivado", "-mode", "batch", "-source", tcl_script]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=3600)
            
            if result.returncode == 0:
                print("✓ FPGA compilation successful")
                return True
            else:
                print("✗ FPGA compilation failed")
                print(result.stderr)
                return False
                
        except subprocess.TimeoutExpired:
            print("✗ FPGA compilation timed out")
            return False
        except FileNotFoundError:
            print("✗ Vivado not found in PATH")
            return False
    
    def generate_compile_script(self):
        """生成Vivado编译脚本"""
        script_content = f"""
# 自动生成的Vivado脚本
set project_name {self.config["project"]["name"]}
set top_level {self.config["project"]["top"]}
set part_name {self.config["project"]["part"]}
set rtl_dir {self.config["project"]["rtl_dir"]}
set constraint_file {self.config["project"]["constraint_file"]}

# 创建项目
create_project $project_name ./temp_project -part $part_name

# 添加RTL文件
set rtl_files [glob $rtl_dir/*.v $rtl_dir/*.sv]
foreach file $rtl_files {{
    add_files -norecurse $file
}}

# 添加约束文件
add_files -fileset constrs_1 -force $constraint_file

# 综合
synth_design -top $top_level -part $part_name

# 优化
opt_design
power_opt_design

# 布局布线
place_design
phys_opt_design
route_design

# 报告
report_utilization -file reports/utilization.txt
report_timing_summary -file reports/timing.txt
report_drc -file reports/drc.txt

# 生成bitstream
write_bitstream $project_name.bit

# 关闭项目
close_project
"""
        
        script_file = "temp_compile.tcl"
        with open(script_file, 'w') as f:
            f.write(script_content)
        
        return script_file
    
    def download_bitstream(self, bitstream_file=None):
        """下载bitstream到FPGA"""
        if bitstream_file is None:
            bitstream_file = f"{self.config['project']['name']}.bit"
        
        print(f"Downloading bitstream: {bitstream_file}")
        
        tcl_script = f"""
# 连接硬件
open_hw_manager
connect_hw_server
open_hw_target

# 获取设备
current_hw_device [get_hw_devices *]
set_property PROGRAM.FILE {{{bitstream_file}}} [current_hw_device]

# 编程
program_hw_devices [current_hw_device]

# 验证
refresh_hw_device [current_hw_device]

close_hw_target
close_hw_manager
"""
        
        script_file = "temp_download.tcl"
        with open(script_file, 'w') as f:
            f.write(tcl_script)
        
        try:
            cmd = ["vivado", "-mode", "batch", "-source", script_file]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
            
            if result.returncode == 0:
                print("✓ Bitstream downloaded successfully")
                return True
            else:
                print("✗ Bitstream download failed")
                print(result.stderr)
                return False
                
        except subprocess.TimeoutExpired:
            print("✗ Bitstream download timed out")
            return False
    
    def run_test(self, test_name):
        """运行单个测试"""
        print(f"Running test: {test_name}")
        
        test_file = os.path.join(self.config["tests"]["dir"], f"{test_name}.py")
        
        if not os.path.exists(test_file):
            print(f"✗ Test file not found: {test_file}")
            return False
        
        try:
            start_time = time.time()
            result = subprocess.run(
                ["python", test_file],
                capture_output=True,
                text=True,
                timeout=self.config["tests"]["timeout"]
            )
            end_time = time.time()
            
            duration = end_time - start_time
            
            if result.returncode == 0:
                print(f"✓ Test {test_name} PASSED ({duration:.2f}s)")
                self.results.append({
                    "name": test_name,
                    "status": "PASSED",
                    "duration": duration,
                    "timestamp": datetime.now().isoformat()
                })
                return True
            else:
                print(f"✗ Test {test_name} FAILED ({duration:.2f}s)")
                print(result.stderr)
                self.results.append({
                    "name": test_name,
                    "status": "FAILED",
                    "duration": duration,
                    "timestamp": datetime.now().isoformat(),
                    "error": result.stderr
                })
                return False
                
        except subprocess.TimeoutExpired:
            print(f"✗ Test {test_name} timed out")
            self.results.append({
                "name": test_name,
                "status": "TIMEOUT",
                "duration": self.config["tests"]["timeout"],
                "timestamp": datetime.now().isoformat()
            })
            return False
    
    def run_regression(self):
        """运行回归测试"""
        print("Starting regression test...")
        
        tests_dir = self.config["tests"]["dir"]
        test_files = glob.glob(os.path.join(tests_dir, "*.py"))
        
        passed = 0
        failed = 0
        
        for test_file in test_files:
            test_name = os.path.splitext(os.path.basename(test_file))[0]
            if self.run_test(test_name):
                passed += 1
            else:
                failed += 1
        
        total = passed + failed
        print(f"\nRegression summary: {passed}/{total} passed")
        
        return failed == 0
    
    def generate_report(self):
        """生成测试报告"""
        report_file = os.path.join(
            self.config["reports"]["dir"],
            f"test_report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        )
        
        report = {
            "timestamp": datetime.now().isoformat(),
            "project": self.config["project"]["name"],
            "results": self.results,
            "summary": {
                "total": len(self.results),
                "passed": sum(1 for r in self.results if r["status"] == "PASSED"),
                "failed": sum(1 for r in self.results if r["status"] == "FAILED"),
                "timeout": sum(1 for r in self.results if r["status"] == "TIMEOUT")
            }
        }
        
        with open(report_file, 'w') as f:
            json.dump(report, f, indent=2)
        
        print(f"✓ Report generated: {report_file}")
        
        # 打印摘要
        print("\n" + "="*50)
        print("TEST SUMMARY")
        print("="*50)
        print(f"Total tests: {report['summary']['total']}")
        print(f"Passed: {report['summary']['passed']}")
        print(f"Failed: {report['summary']['failed']}")
        print(f"Timeout: {report['summary']['timeout']}")
        print("="*50)

def main():
    parser = argparse.ArgumentParser(description='FPGA原型验证自动化工具')
    parser.add_argument('command', choices=['compile', 'download', 'test', 'regression', 'report'],
                       help='要执行的命令')
    parser.add_argument('--test', help='测试名称（用于test命令）')
    parser.add_argument('--bitstream', help='bitstream文件路径（用于download命令）')
    parser.add_argument('--config', default='fpga_config.json', help='配置文件路径')
    
    args = parser.parse_args()
    
    validator = FPGAValidator(args.config)
    
    if args.command == 'compile':
        success = validator.compile_fpga()
        sys.exit(0 if success else 1)
    
    elif args.command == 'download':
        success = validator.download_bitstream(args.bitstream)
        sys.exit(0 if success else 1)
    
    elif args.command == 'test':
        if not args.test:
            print("Error: --test argument required for test command")
            sys.exit(1)
        success = validator.run_test(args.test)
        sys.exit(0 if success else 1)
    
    elif args.command == 'regression':
        success = validator.run_regression()
        validator.generate_report()
        sys.exit(0 if success else 1)
    
    elif args.command == 'report':
        validator.generate_report()
        sys.exit(0)

if __name__ == '__main__':
    import glob
    main()
