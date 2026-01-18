#!/usr/bin/env python3
"""
YaoGuang SoC DV回归测试执行框架
===========================

功能:
- 自动发现测试用例
- 并行执行测试
- 收集覆盖率
- 生成报告
- 失败通知

用法:
    python run_regression.py --suite sanity
    python run_regression.py --suite nightly --parallel 16
    python run_regression.py --suite weekly --retry 2
    python run_regression.py --all --email-on-failure

作者: YaoGuang DV Team
日期: 2026-01-18
"""

import os
import sys
import argparse
import subprocess
import yaml
import json
import time
import datetime
import signal
import threading
import queue
import smtplib
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from pathlib import Path
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Tuple
from concurrent.futures import ThreadPoolExecutor, as_completed
from enum import Enum
import logging

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler(),
        logging.FileHandler('regression.log')
    ]
)
logger = logging.getLogger(__name__)


class TestStatus(Enum):
    """测试状态枚举"""
    PENDING = "pending"
    RUNNING = "running"
    PASSED = "passed"
    FAILED = "failed"
    SKIPPED = "skipped"
    TIMEOUT = "timeout"
    ERROR = "error"


@dataclass
class TestResult:
    """测试结果数据类"""
    test_name: str
    module: str
    status: TestStatus
    start_time: datetime.datetime
    end_time: Optional[datetime.datetime] = None
    duration: Optional[float] = None
    log_file: Optional[str] = None
    wave_file: Optional[str] = None
    coverage_file: Optional[str] = None
    error_message: Optional[str] = None
    return_code: Optional[int] = None
    retry_count: int = 0
    priority: str = "P1"
    tier: str = "functional"


@dataclass
class RegressionConfig:
    """回归测试配置"""
    suite_name: str
    tests: List[Dict]
    parallel_jobs: int = 8
    pass_threshold: float = 95.0
    timeout: int = 3600
    sim_tool: str = "vcs"
    coverage_types: List[str] = field(default_factory=lambda: ["line", "branch", "condition", "toggle", "fsm", "assertion"])
    output_dir: str = "coverage_regressions/regression"
    email_on_failure: bool = True
    max_retries: int = 2


class RegressionRunner:
    """回归测试运行器"""
    
    def __init__(self, config_path: str = "master_regression.yaml"):
        self.config_path = config_path
        self.config: Dict = {}
        self.test_results: Dict[str, TestResult] = {}
        self.current_suite: Optional[str] = None
        self.start_time: Optional[datetime.datetime] = None
        self.lock = threading.Lock()
        self.result_queue = queue.Queue()
        
        # 加载配置
        self.load_config()
    
    def load_config(self) -> None:
        """加载回归配置"""
        logger.info(f"加载配置文件: {self.config_path}")
        with open(self.config_path, 'r') as f:
            self.config = yaml.safe_load(f)
        logger.info("配置加载完成")
    
    def discover_tests(self, suite_name: str) -> List[Dict]:
        """发现测试用例"""
        logger.info(f"发现测试用例: {suite_name}")
        
        suite_config = self.config.get('regression_suites', {}).get(suite_name)
        if not suite_config:
            raise ValueError(f"未找到回归套件配置: {suite_name}")
        
        tests = suite_config.get('tests', [])
        expanded_tests = []
        
        for test in tests:
            # 处理include关键字
            if 'include' in test:
                include_name = test['include']
                included_tests = self.discover_tests(include_name)
                expanded_tests.extend(included_tests)
            else:
                expanded_tests.append(test)
        
        logger.info(f"发现 {len(expanded_tests)} 个测试用例")
        return expanded_tests
    
    def get_module_tests_dir(self, module: str) -> str:
        """获取模块测试目录"""
        modules_config = self.config.get('modules', {})
        module_config = modules_config.get(module, {})
        return module_config.get('tests_dir', f"tests/{module}")
    
    def build_test_command(self, test: Dict, result: TestResult) -> List[str]:
        """构建测试命令"""
        sim_tool = self.config.get('execution', {}).get('sim_tool', 'vcs')
        module = test.get('module', 'unknown')
        test_name = test.get('name', 'unknown')
        tier = test.get('tier', 'functional')
        
        tests_dir = self.get_module_tests_dir(module)
        test_file = os.path.join(tests_dir, f"{test_name}.sv")
        
        # 基本命令结构
        if sim_tool == 'vcs':
            cmd = [
                'vcs',
                '-full64',
                '-sverilog',
                '-debug_access+all',
                '-lca',
                f'-timescale=1ns/1ps',
                '-top', f'{module}_top',
                '+incdir+{tests_dir}',
                f'{tests_dir}/tb_{module}.sv',
                f'{test_file}',
                '-o', f'simv_{test_name}'
            ]
        
        elif sim_tool == 'xcelium':
            cmd = [
                'xrun',
                '-sv',
                '-access +rwc',
                '-top', f'{module}_top',
                '-incdir', tests_dir,
                f'{tests_dir}/tb_{module}.sv',
                f'{test_file}'
            ]
        
        elif sim_tool == 'riviera':
            cmd = [
                'riviera',
                '-sv',
                '-top', f'{module}_top',
                '-incdir', tests_dir,
                f'{tests_dir}/tb_{module}.sv',
                f'{test_file}'
            ]
        
        else:
            raise ValueError(f"不支持的仿真工具: {sim_tool}")
        
        # 添加覆盖率选项
        coverage_types = self.config.get('execution', {}).get('coverage', {}).get('type', [])
        for cov_type in coverage_types:
            cmd.append(f'+cover={cov_type}')
        
        # 添加日志选项
        log_file = f"logs/{test_name}.log"
        cmd.extend(['-l', log_file])
        
        # 添加波浪选项
        waves_config = self.config.get('execution', {}).get('waves', 'auto')
        if waves_config in ['auto', 'always']:
            cmd.extend(['-assert', 'debug'])
        
        return cmd
    
    def run_single_test(self, test: Dict, max_retries: int = 2) -> TestResult:
        """运行单个测试"""
        test_name = test.get('name', 'unknown')
        module = test.get('module', 'unknown')
        timeout = test.get('timeout', self.config.get('execution', {}).get('default_timeout', 3600))
        tier = test.get('tier', 'functional')
        priority = test.get('priority', 'P1')
        
        result = TestResult(
            test_name=test_name,
            module=module,
            status=TestStatus.RUNNING,
            start_time=datetime.datetime.now(),
            priority=priority,
            tier=tier
        )
        
        # 创建日志目录
        os.makedirs('logs', exist_ok=True)
        
        cmd = self.build_test_command(test, result)
        log_file = f"logs/{test_name}.log"
        
        for retry in range(max_retries):
            try:
                logger.info(f"执行测试: {test_name} (尝试 {retry + 1}/{max_retries})")
                
                process = subprocess.Popen(
                    cmd,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    text=True,
                    preexec_fn=os.setsid
                )
                
                # 等待超时
                try:
                    stdout, _ = process.communicate(timeout=timeout)
                    result.return_code = process.returncode
                    
                    # 写入日志
                    with open(log_file, 'w') as f:
                        f.write(stdout)
                    
                    if process.returncode == 0:
                        result.status = TestStatus.PASSED
                        logger.info(f"测试通过: {test_name}")
                    else:
                        result.status = TestStatus.FAILED
                        result.error_message = f"返回码: {process.returncode}"
                        logger.error(f"测试失败: {test_name}, 返回码: {process.returncode}")
                
                except subprocess.TimeoutExpired:
                    os.killpg(os.getpgid(process.pid), signal.SIGTERM)
                    result.status = TestStatus.TIMEOUT
                    result.error_message = f"超时: {timeout}秒"
                    logger.error(f"测试超时: {test_name}")
                    
                    # 杀掉进程
                    process.kill()
                    process.communicate()
            
            except Exception as e:
                result.status = TestStatus.ERROR
                result.error_message = str(e)
                logger.error(f"测试错误: {test_name}, 错误: {e}")
            
            # 检查是否需要重试
            if result.status in [TestStatus.PASSED]:
                break
            elif retry < max_retries - 1:
                result.retry_count += 1
                time.sleep(60)  # 重试前等待
        
        result.end_time = datetime.datetime.now()
        if result.start_time and result.end_time:
            result.duration = (result.end_time - result.start_time).total_seconds()
        
        result.log_file = log_file
        
        # 收集覆盖率
        self.collect_coverage(test, result)
        
        return result
    
    def collect_coverage(self, test: Dict, result: TestResult) -> None:
        """收集覆盖率数据"""
        test_name = test.get('name', 'unknown')
        coverage_dir = f"coverage/{test_name}"
        os.makedirs(coverage_dir, exist_ok=True)
        
        # 使用urg合并覆盖率
        coverage_types = self.config.get('execution', {}).get('coverage', {}).get('type', [])
        
        try:
            cmd = [
                'urg',
                '-dir', f'simv.vdb',
                '-dir', f'{test_name}.vdb',
                '-report', coverage_dir,
                '-format', 'both',
                '-metric', 'hierarchy'
            ]
            
            for cov_type in coverage_types:
                cmd.extend(['-'+cov_type])
            
            subprocess.run(cmd, capture_output=True, timeout=600)
            
            result.coverage_file = coverage_dir
            logger.info(f"覆盖率收集完成: {test_name}")
        
        except Exception as e:
            logger.warning(f"覆盖率收集失败: {test_name}, 错误: {e}")
    
    def run_regression(self, suite_name: str, parallel_jobs: int = 8, 
                       max_retries: int = 2, output_dir: str = None) -> Tuple[bool, Dict]:
        """运行回归测试套件"""
        self.current_suite = suite_name
        self.start_time = datetime.datetime.now()
        
        logger.info(f"开始执行回归测试套件: {suite_name}")
        logger.info(f"并行度: {parallel_jobs}, 最大重试次数: {max_retries}")
        
        # 获取测试列表
        tests = self.discover_tests(suite_name)
        
        # 创建输出目录
        if output_dir is None:
            output_dir = f"{self.config.get('reporting', {}).get('output_dir', 'coverage_regressions/regression')}/{suite_name}"
        os.makedirs(output_dir, exist_ok=True)
        
        # 并行执行测试
        results = []
        with ThreadPoolExecutor(max_workers=parallel_jobs) as executor:
            futures = {
                executor.submit(self.run_single_test, test, max_retries): test 
                for test in tests
            }
            
            for future in as_completed(futures):
                test = futures[future]
                try:
                    result = future.result()
                    results.append(result)
                    self.test_results[result.test_name] = result
                    
                    # 实时日志
                    with self.lock:
                        logger.info(f"完成: {result.test_name} - {result.status.value}")
                
                except Exception as e:
                    logger.error(f"测试执行异常: {e}")
                    test_name = test.get('name', 'unknown')
                    error_result = TestResult(
                        test_name=test_name,
                        module=test.get('module', 'unknown'),
                        status=TestStatus.ERROR,
                        start_time=datetime.datetime.now(),
                        error_message=str(e)
                    )
                    results.append(error_result)
        
        # 统计结果
        stats = self.calculate_statistics(results)
        
        # 生成报告
        report_path = self.generate_report(suite_name, results, stats, output_dir)
        
        # 合并覆盖率
        self.merge_coverage(suite_name, output_dir)
        
        # 检查通过率
        pass_threshold = self.config.get('regression_suites', {}).get(suite_name, {}).get('pass_threshold', 95.0)
        passed = stats['pass_rate'] >= pass_threshold
        
        # 失败通知
        if not passed and self.config.get('execution', {}).get('email_on_failure', True):
            self.send_failure_notification(suite_name, stats, report_path)
        
        logger.info(f"回归测试完成: {suite_name}")
        logger.info(f"通过率: {stats['pass_rate']:.2f}% (阈值: {pass_threshold}%)")
        logger.info(f"报告: {report_path}")
        
        return passed, stats
    
    def calculate_statistics(self, results: List[TestResult]) -> Dict:
        """计算统计信息"""
        total = len(results)
        passed = sum(1 for r in results if r.status == TestStatus.PASSED)
        failed = sum(1 for r in results if r.status == TestStatus.FAILED)
        timeout = sum(1 for r in results if r.status == TestStatus.TIMEOUT)
        error = sum(1 for r in results if r.status == TestStatus.ERROR)
        skipped = sum(1 for r in results if r.status == TestStatus.SKIPPED)
        
        pass_rate = (passed / total * 100) if total > 0 else 0
        
        # 按模块统计
        module_stats = {}
        for r in results:
            if r.module not in module_stats:
                module_stats[r.module] = {'total': 0, 'passed': 0, 'failed': 0}
            module_stats[r.module]['total'] += 1
            if r.status == TestStatus.PASSED:
                module_stats[r.module]['passed'] += 1
            else:
                module_stats[r.module]['failed'] += 1
        
        # 按层级统计
        tier_stats = {}
        for r in results:
            if r.tier not in tier_stats:
                tier_stats[r.tier] = {'total': 0, 'passed': 0}
            tier_stats[r.tier]['total'] += 1
            if r.status == TestStatus.PASSED:
                tier_stats[r.tier]['passed'] += 1
        
        return {
            'total': total,
            'passed': passed,
            'failed': failed,
            'timeout': timeout,
            'error': error,
            'skipped': skipped,
            'pass_rate': pass_rate,
            'module_stats': module_stats,
            'tier_stats': tier_stats,
            'duration': (datetime.datetime.now() - self.start_time).total_seconds() if self.start_time else 0
        }
    
    def generate_report(self, suite_name: str, results: List[TestResult], 
                        stats: Dict, output_dir: str) -> str:
        """生成回归测试报告"""
        report_path = os.path.join(output_dir, f"report_{suite_name}.md")
        
        # 加载报告模板
        template_path = self.config.get('reporting', {}).get('report_template', 'regression_report_template.md')
        
        report_content = f"""# YaoGuang SoC 回归测试报告

## 执行摘要

| 指标 | 值 |
|------|-----|
| 回归套件 | {suite_name} |
| 执行时间 | {datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')} |
| 总测试数 | {stats['total']} |
| 通过 | {stats['passed']} |
| 失败 | {stats['failed']} |
| 超时 | {stats['timeout']} |
| 错误 | {stats['error']} |
| 通过率 | {stats['pass_rate']:.2f}% |
| 执行时长 | {stats['duration']:.0f}秒 |

## 通过率统计

```
通过率: {stats['pass_rate']:.2f}%
{'█' * int(stats['pass_rate'] / 5)}{'░' * (20 - int(stats['pass_rate'] / 5))}
```

## 模块级统计

| 模块 | 总数 | 通过 | 失败 | 通过率 |
|------|------|------|------|--------|
"""
        
        for module, module_stat in sorted(stats['module_stats'].items()):
            pass_rate = (module_stat['passed'] / module_stat['total'] * 100) if module_stat['total'] > 0 else 0
            report_content += f"| {module} | {module_stat['total']} | {module_stat['passed']} | {module_stat['failed']} | {pass_rate:.1f}% |\n"
        
        report_content += """
## 层级级统计

| 层级 | 总数 | 通过 | 通过率 |
|------|------|------|--------|
"""
        
        for tier, tier_stat in sorted(stats['tier_stats'].items()):
            pass_rate = (tier_stat['passed'] / tier_stat['total'] * 100) if tier_stat['total'] > 0 else 0
            report_content += f"| {tier} | {tier_stat['total']} | {tier_stat['passed']} | {pass_rate:.1f}% |\n"
        
        report_content += """
## 失败测试列表

| 测试名称 | 模块 | 状态 | 错误信息 | 时长(秒) |
|----------|------|------|----------|----------|
"""
        
        failed_tests = [r for r in results if r.status != TestStatus.PASSED]
        for r in failed_tests:
            error_msg = r.error_message[:50] if r.error_message else '-'
            duration = r.duration if r.duration else 0
            report_content += f"| {r.test_name} | {r.module} | {r.status.value} | {error_msg} | {duration:.0f} |\n"
        
        report_content += """
## 测试详情

"""
        
        for r in results:
            status_icon = "✅" if r.status == TestStatus.PASSED else "❌" if r.status in [TestStatus.FAILED, TestStatus.TIMEOUT, TestStatus.ERROR] else "⏭️"
            report_content += f"### {status_icon} {r.test_name}\n\n"
            report_content += f"- **模块**: {r.module}\n"
            report_content += f"- **层级**: {r.tier}\n"
            report_content += f"- **优先级**: {r.priority}\n"
            report_content += f"- **状态**: {r.status.value}\n"
            report_content += f"- **时长**: {r.duration:.2f}秒\n" if r.duration else ""
            if r.error_message:
                report_content += f"- **错误**: {r.error_message}\n"
            report_content += f"- **日志**: {r.log_file}\n" if r.log_file else ""
            report_content += f"- **覆盖率**: {r.coverage_file}\n" if r.coverage_file else ""
            report_content += "\n"
        
        report_content += f"""
## 覆盖率汇总

覆盖率报告请参考: `{output_dir}/coverage_report.html`

## 建议

"""
        
        if stats['pass_rate'] < 90:
            report_content += "⚠️ **严重警告**: 通过率低于90%，需要立即调查失败原因。\n\n"
        elif stats['pass_rate'] < 95:
            report_content += "⚠️ **警告**: 通过率低于95%，建议检查失败测试。\n\n"
        else:
            report_content += "✅ **通过**: 所有测试通过或通过率在可接受范围内。\n\n"
        
        report_content += f"""
---
*报告生成时间: {datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')}*
*YaoGuang SoC DV验证团队*
"""
        
        with open(report_path, 'w', encoding='utf-8') as f:
            f.write(report_content)
        
        # 同时生成HTML报告
        self.generate_html_report(suite_name, results, stats, output_dir)
        
        return report_path
    
    def generate_html_report(self, suite_name: str, results: List[TestResult], 
                             stats: Dict, output_dir: str) -> str:
        """生成HTML格式报告"""
        html_path = os.path.join(output_dir, f"report_{suite_name}.html")
        
        html_content = f"""<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>YaoGuang SoC 回归测试报告 - {suite_name}</title>
    <style>
        body {{ font-family: 'Segoe UI', Arial, sans-serif; margin: 20px; background-color: #f5f5f5; }}
        .container {{ max-width: 1200px; margin: 0 auto; background: white; padding: 20px; border-radius: 8px; box-shadow: 0 2px 4px rgba(0,0,0,0.1); }}
        h1 {{ color: #333; border-bottom: 3px solid #0078d4; padding-bottom: 10px; }}
        h2 {{ color: #444; margin-top: 30px; }}
        .summary-box {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(200px, 1fr)); gap: 15px; margin: 20px 0; }}
        .stat-card {{ background: linear-gradient(135deg, #667eea 0%, #764ba2 100%); color: white; padding: 20px; border-radius: 8px; text-align: center; }}
        .stat-card.pass {{ background: linear-gradient(135deg, #11998e 0%, #38ef7d 100%); }}
        .stat-card.fail {{ background: linear-gradient(135deg, #eb3349 0%, #f45c43 100%); }}
        .stat-value {{ font-size: 36px; font-weight: bold; }}
        .stat-label {{ font-size: 14px; opacity: 0.9; }}
        table {{ width: 100%; border-collapse: collapse; margin: 15px 0; }}
        th, td {{ padding: 12px; text-align: left; border-bottom: 1px solid #ddd; }}
        th {{ background-color: #0078d4; color: white; }}
        tr:hover {{ background-color: #f5f5f5; }}
        .pass {{ color: #28a745; font-weight: bold; }}
        .fail {{ color: #dc3545; font-weight: bold; }}
        .progress-bar {{ background-color: #e9ecef; border-radius: 4px; height: 20px; overflow: hidden; }}
        .progress-fill {{ height: 100%; background: linear-gradient(90deg, #0078d4, #00bcf2); transition: width 0.3s; }}
        .test-passed {{ background-color: #d4edda; }}
        .test-failed {{ background-color: #f8d7da; }}
        .log-content {{ background: #1e1e1e; color: #d4d4d4; padding: 15px; border-radius: 4px; font-family: 'Consolas', monospace; font-size: 12px; max-height: 300px; overflow-y: auto; }}
    </style>
</head>
<body>
    <div class="container">
        <h1>🚗 YaoGuang SoC 回归测试报告</h1>
        <p><strong>回归套件:</strong> {suite_name}</p>
        <p><strong>执行时间:</strong> {datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')}</p>
        
        <div class="summary-box">
            <div class="stat-card">
                <div class="stat-value">{stats['total']}</div>
                <div class="stat-label">总测试数</div>
            </div>
            <div class="stat-card pass">
                <div class="stat-value">{stats['passed']}</div>
                <div class="stat-label">通过</div>
            </div>
            <div class="stat-card fail">
                <div class="stat-value">{stats['failed'] + stats['timeout'] + stats['error']}</div>
                <div class="stat-label">失败</div>
            </div>
            <div class="stat-card">
                <div class="stat-value">{stats['pass_rate']:.1f}%</div>
                <div class="stat-label">通过率</div>
            </div>
        </div>
        
        <h2>📊 模块级统计</h2>
        <table>
            <tr><th>模块</th><th>总数</th><th>通过</th><th>失败</th><th>通过率</th></tr>
"""
        
        for module, module_stat in sorted(stats['module_stats'].items()):
            pass_rate = (module_stat['passed'] / module_stat['total'] * 100) if module_stat['total'] > 0 else 0
            pass_class = "pass" if pass_rate >= 95 else ("fail" if pass_rate < 80 else "")
            html_content += f"""            <tr>
                <td>{module}</td>
                <td>{module_stat['total']}</td>
                <td class="pass">{module_stat['passed']}</td>
                <td class="fail">{module_stat['failed']}</td>
                <td class="{pass_class}">{pass_rate:.1f}%</td>
            </tr>
"""
        
        html_content += """        </table>
        
        <h2>📋 测试详情</h2>
        <table>
            <tr><th>测试名称</th><th>模块</th><th>层级</th><th>状态</th><th>时长</th></tr>
"""
        
        for r in results:
            status_class = "test-passed" if r.status == TestStatus.PASSED else "test-failed"
            status_text = "✅ 通过" if r.status == TestStatus.PASSED else "❌ 失败"
            duration = f"{r.duration:.1f}s" if r.duration else "-"
            html_content += f"""            <tr class="{status_class}">
                <td>{r.test_name}</td>
                <td>{r.module}</td>
                <td>{r.tier}</td>
                <td>{status_text}</td>
                <td>{duration}</td>
            </tr>
"""
        
        html_content += """        </table>
        
        <footer>
            <p style="text-align: center; color: #666; margin-top: 40px;">
                YaoGuang SoC DV验证团队 | 报告生成时间: """ + datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S') + """
            </p>
        </footer>
    </div>
</body>
</html>
"""
        
        with open(html_path, 'w', encoding='utf-8') as f:
            f.write(html_content)
        
        return html_path
    
    def merge_coverage(self, suite_name: str, output_dir: str) -> None:
        """合并覆盖率数据"""
        logger.info(f"合并覆盖率数据: {suite_name}")
        
        coverage_dir = os.path.join(output_dir, "coverage")
        os.makedirs(coverage_dir, exist_ok=True)
        
        # 查找所有覆盖率数据库
        vdb_files = list(Path('.').glob('*.vdb'))
        
        if vdb_files:
            try:
                cmd = [
                    'urg',
                    '-dir', ' '.join([str(f) for f in vdb_files]),
                    '-report', coverage_dir,
                    '-format', 'both',
                    '-metric', 'hierarchy'
                ]
                
                subprocess.run(cmd, capture_output=True, timeout=600)
                logger.info(f"覆盖率报告生成: {coverage_dir}")
            
            except Exception as e:
                logger.warning(f"覆盖率合并失败: {e}")
        else:
            logger.info("未找到覆盖率数据库文件")
    
    def send_failure_notification(self, suite_name: str, stats: Dict, report_path: str) -> None:
        """发送失败通知"""
        email_config = self.config.get('execution', {}).get('failure_notification', [])
        
        if not email_config:
            return
        
        subject = f"[YaoGuang DV] 回归测试失败 - {suite_name}"
        
        body = f"""
YaoGuang SoC 回归测试失败通知

回归套件: {suite_name}
执行时间: {datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

统计信息:
- 总测试数: {stats['total']}
- 通过: {stats['passed']}
- 失败: {stats['failed']}
- 超时: {stats['timeout']}
- 通过率: {stats['pass_rate']:.2f}%

失败测试列表:
"""
        
        for r in self.test_results.values():
            if r.status != TestStatus.PASSED:
                body += f"- {r.test_name} ({r.module}): {r.status.value}\n"
                if r.error_message:
                    body += f"  错误: {r.error_message}\n"
        
        body += f"""
完整报告: {report_path}

请登录验证服务器查看详细日志和波形文件。

---
YaoGuang DV验证自动化系统
"""
        
        # 简化版本: 仅打印通知
        logger.warning("=" * 60)
        logger.warning("回归测试失败通知")
        logger.warning("=" * 60)
        logger.warning(body)
        logger.warning("=" * 60)
    
    def upload_results_to_database(self, suite_name: str, stats: Dict) -> None:
        """上传结果到数据库"""
        db_config = self.config.get('reporting', {}).get('database', {})
        
        if not db_config:
            return
        
        logger.info(f"上传结果到数据库: {db_config.get('database', 'N/A')}")
        
        # 这里可以添加InfluxDB或其他数据库的写入逻辑
        # 示例代码:
        # from influxdb import InfluxDBClient
        # client = InfluxDBClient(db_config['url'].split(':')[0], int(db_config['url'].split(':')[1]))
        # client.switch_database(db_config['database'])
        # json_body = [
        #     {
        #         "measurement": "regression_results",
        #         "tags": {
        #             "suite": suite_name
        #         },
        #         "fields": stats
        #     }
        # ]
        # client.write_points(json_body)


def main():
    """主函数"""
    parser = argparse.ArgumentParser(description='YaoGuang SoC DV回归测试框架')
    parser.add_argument('--suite', type=str, default='sanity',
                        choices=['sanity', 'nightly', 'weekly', 'full'],
                        help='回归测试套件 (默认: sanity)')
    parser.add_argument('--parallel', type=int, default=8,
                        help='并行度 (默认: 8)')
    parser.add_argument('--retry', type=int, default=2,
                        help='最大重试次数 (默认: 2)')
    parser.add_argument('--output', type=str, default=None,
                        help='输出目录')
    parser.add_argument('--config', type=str, default='master_regression.yaml',
                        help='配置文件路径')
    parser.add_argument('--all', action='store_true',
                        help='执行所有回归套件')
    parser.add_argument('--email-on-failure', action='store_true', default=True,
                        help='失败时发送邮件通知')
    
    args = parser.parse_args()
    
    # 创建运行器
    runner = RegressionRunner(args.config)
    
    # 执行回归
    if args.all:
        suites = ['sanity', 'nightly', 'weekly', 'full']
        all_passed = True
        
        for suite in suites:
            passed, stats = runner.run_regression(
                suite,
                parallel_jobs=args.parallel,
                max_retries=args.retry,
                output_dir=args.output
            )
            
            if not passed:
                all_passed = False
        
        sys.exit(0 if all_passed else 1)
    
    else:
        passed, stats = runner.run_regression(
            args.suite,
            parallel_jobs=args.parallel,
            max_retries=args.retry,
            output_dir=args.output
        )
        
        sys.exit(0 if passed else 1)


if __name__ == '__main__':
    main()
