#!/usr/bin/env python3
"""
YaoGuang SoC DV 验证环境运行脚本
支持仿真、回归测试、覆盖率收集
"""

import os
import sys
import argparse
import subprocess
import yaml
from datetime import datetime
from pathlib import Path


class DVVerificationEnv:
    """DV 验证环境管理类"""

    def __init__(self):
        self.root_dir = Path(__file__).parent.parent.parent
        self.uvm_env = self.root_dir / "05_Verification_DV" / "uvm_env"
        self.tests_dir = self.root_dir / "05_Verification_DV" / "tests"
        self.regression_dir = self.root_dir / "05_Verification_DV" / "regression"
        self.coverage_dir = self.uvm_env / "coverage"

        # 工具配置
        self.simulator = os.environ.get("SIMULATOR", "vcs")
        self.sim_options = [
            "-full64",
            "-debug_access+all",
            "+vcs+lic_wait",
        ]

    def compile(self, top_module="top_tb", extra_opts=None):
        """编译验证环境"""
        print(f"[*] Compiling verification environment...")

        compile_cmd = [
            self.simulator,
            "-full64",
            "-sverilog",
            "-f", str(self.uvm_env / "filelist" / "uvm.f"),
            "-top", top_module,
        ]

        if extra_opts:
            compile_cmd.extend(extra_opts)

        result = subprocess.run(compile_cmd, cwd=self.uvm_env)
        return result.returncode == 0

    def run_test(self, test_name, seed=None, wave=False, extra_opts=None):
        """运行单个测试"""
        print(f"[*] Running test: {test_name}")

        run_cmd = [
            self.simulator,
            "-ucli",
            "-do", f"run -simulate +UVM_TESTNAME={test_name}",
        ]

        if seed:
            run_cmd.extend(["+ntb_random_seed={seed}"])

        if wave:
            run_cmd.extend(["+dump_vcd+dump.vcd"])

        if extra_opts:
            run_cmd.extend(extra_opts)

        result = subprocess.run(run_cmd)
        return result.returncode == 0

    def run_regression(self, regression_name="nightly"):
        """运行回归测试"""
        print(f"[*] Running regression: {regression_name}")

        # 加载回归配置
        config_file = self.regression_dir / f"{regression_name}_config.yaml"
        if config_file.exists():
            with open(config_file) as f:
                config = yaml.safe_load(f)
                test_list = config.get("tests", [])
        else:
            # 默认测试列表
            test_list = [
                "test_sanity",
                "test_pmu_basic",
                "test_noc_basic",
            ]

        # 运行所有测试
        passed = 0
        failed = 0

        for test in test_list:
            if self.run_test(test):
                passed += 1
            else:
                failed += 1

        print(f"[*] Regression completed: {passed} passed, {failed} failed")
        return failed == 0

    def collect_coverage(self, test_name=None):
        """收集覆盖率"""
        print(f"[*] Collecting coverage...")

        cov_cmd = [
            "urg",
            "-dir", str(self.uvm_env / "coverage" / "test.vdb"),
            "-report", str(self.uvm_env / "coverage_reports" / test_name or "default"),
        ]

        result = subprocess.run(cov_cmd)
        return result.returncode == 0

    def gen_cov_report(self, test_name=None):
        """生成覆盖率报告"""
        print(f"[*] Generating coverage report...")

        # 生成 HTML 报告
        report_dir = self.root_dir / "05_Verification_DV" / "coverage_reports" / "latest"
        report_dir.mkdir(parents=True, exist_ok=True)

        # 使用 urg 生成报告
        urg_cmd = [
            "urg",
            "-dir", str(self.uvm_env / "coverage" / "*.vdb"),
            "-report", str(report_dir),
            "-format", "html",
        ]

        subprocess.run(urg_cmd)

        # 生成覆盖率摘要
        summary_file = report_dir / "coverage_summary.txt"
        with open(summary_file, "w") as f:
            f.write(f"YaoGuang SoC DV Coverage Summary\n")
            f.write(f"Generated: {datetime.now()}\n")
            f.write(f"================================\n\n")
            f.write("Coverage metrics will be filled after regression\n")

        print(f"[*] Report generated: {report_dir}")
        return True

    def check_signoff(self, module_name):
        """检查模块 sign-off 状态"""
        print(f"[*] Checking sign-off for: {module_name}")

        # 检查覆盖率是否达标
        cov_dir = self.root_dir / "05_Verification_DV" / "coverage_reports" / module_name
        if cov_dir.exists():
            # 读取覆盖率报告
            cov_file = cov_dir / "coverage_summary.txt"
            if cov_file.exists():
                with open(cov_file) as f:
                    content = f.read()
                    if "100%" in content or "95%" in content:
                        print(f"[+] {module_name} coverage requirement met")
                        return True

        print(f"[-] {module_name} coverage requirement not met")
        return False


def main():
    parser = argparse.ArgumentParser(description="YaoGuang SoC DV Verification Environment")
    parser.add_argument("action", choices=["compile", "run", "regression", "coverage", "report", "signoff"],
                        help="Action to perform")
    parser.add_argument("--test", "-t", help="Test name")
    parser.add_argument("--seed", "-s", type=int, help="Random seed")
    parser.add_argument("--wave", "-w", action="store_true", help="Enable wave dump")
    parser.add_argument("--module", "-m", help="Module name for signoff")
    parser.add_argument("--regression", "-r", default="nightly", help="Regression name")

    args = parser.parse_args()

    env = DVVerificationEnv()

    if args.action == "compile":
        success = env.compile()
    elif args.action == "run":
        success = env.run_test(args.test, args.seed, args.wave)
    elif args.action == "regression":
        success = env.run_regression(args.regression)
    elif args.action == "coverage":
        success = env.collect_coverage(args.test)
    elif args.action == "report":
        success = env.gen_cov_report(args.test)
    elif args.action == "signoff":
        success = env.check_signoff(args.module)
    else:
        success = False

    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
