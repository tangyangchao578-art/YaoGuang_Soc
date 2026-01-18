#!/usr/bin/env python3
"""
PPA（性能-功耗-面积）分析工具

分析芯片架构设计的PPA指标，帮助架构师进行设计空间探索和权衡决策。

使用方法：
    python ppa_analyzer.py --config <config_file>

示例：
    python ppa_analyzer.py --config config.yaml
"""

import argparse
import json
from dataclasses import dataclass, asdict
from typing import List, Dict, Optional
from pathlib import Path


@dataclass
class DesignOption:
    """设计方案选项"""
    name: str
    description: str
    ipc: float
    frequency_ghz: float
    power_w: float
    area_mm2: float
    notes: str


def analyze_ppa_tradeoffs(options: List[DesignOption]) -> Dict:
    """
    分析PPA权衡并生成报告。

    参数：
        options: 设计方案列表

    返回：
        分析结果字典
    """
    if not options:
        return {"error": "No design options provided"}

    # 归一化指标（相对于基准）
    baseline = options[0]
    results = {
        "baseline": asdict(baseline),
        "comparisons": []
    }

    for opt in options[1:]:
        comparison = {
            "option": opt.name,
            "performance_ratio": opt.ipc / baseline.ipc,
            "frequency_ratio": opt.frequency_ghz / baseline.frequency_ghz,
            "power_ratio": opt.power_w / baseline.power_w,
            "area_ratio": opt.area_mm2 / baseline.area_mm2,
            "ppa_score": (
                (opt.ipc / baseline.ipc) *
                (baseline.power_w / opt.power_w) *
                (baseline.area_mm2 / opt.area_mm2)
            )
        }
        results["comparisons"].append(comparison)

    return results


def generate_report(results: Dict) -> str:
    """
    生成PPA分析报告。

    参数：
        results: 分析结果

    返回：
        报告字符串
    """
    report = """# PPA 分析报告

## 基准设计

| 指标 | 值 |
|------|-----|
| IPC | {baseline[ipc]:.2f} |
| 频率 | {baseline[frequency_ghz]:.2f} GHz |
| 功耗 | {baseline[power_w]:.2f} W |
| 面积 | {baseline[area_mm2]:.2f} mm² |
{baseline[notes]}

---

## 设计对比

| 方案 | 性能比 | 频率比 | 功耗比 | 面积比 | PPA分数 |
|------|---------|---------|--------|--------|---------|
""".format(baseline=results["baseline"])

    for comp in results["comparisons"]:
        report += """| {option} | {performance_ratio:.2f}x | {frequency_ratio:.2f}x | {power_ratio:.2f}x | {area_ratio:.2f}x | {ppa_score:.2f}x |
""".format(**comp)

    # 识别最佳选项
    best_ppa = max(results["comparisons"], key=lambda x: x["ppa_score"])
    report += f"""

## 推荐

**最佳PPA方案**: {best_ppa["option"]}

理由：
- PPA分数最高 ({best_ppa["ppa_score"]:.2f}x)
- 性能提升 {best_ppa["performance_ratio"]:.2f}x
- 功耗降低 {(1 - 1/best_ppa["power_ratio"])*100:.1f}%
- 面积增加 {(best_ppa["area_ratio"] - 1)*100:.1f}%

---

*报告由 chip-architect skill 生成*
"""

    return report


def load_config(config_path: Path) -> List[DesignOption]:
    """
    从配置文件加载设计方案。

    参数：
        config_path: 配置文件路径

    返回：
        设计方案列表
    """
    if config_path.suffix == '.json':
        with open(config_path, 'r', encoding='utf-8') as f:
            data = json.load(f)
        return [DesignOption(**opt) for opt in data.get('options', [])]
    else:
        # 简化处理：使用示例数据
        return [
            DesignOption(
                name="基准",
                description="5级流水线，32KB L1 Cache",
                ipc=1.0,
                frequency_ghz=2.0,
                power_w=5.0,
                area_mm2=10.0,
                notes="当前架构设计"
            ),
            DesignOption(
                name="选项A",
                description="7级流水线，64KB L1 Cache",
                ipc=1.15,
                frequency_ghz=2.2,
                power_w=6.5,
                area_mm2=12.0,
                notes="更深的流水线，更大缓存"
            ),
            DesignOption(
                name="选项B",
                description="双发射流水线，32KB L1 Cache",
                ipc=1.25,
                frequency_ghz=1.8,
                power_w=7.0,
                area_mm2=14.0,
                notes="乱序执行，面积增加"
            ),
        ]


def main():
    parser = argparse.ArgumentParser(
        description="芯片设计PPA分析工具",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--config", help="设计方案配置文件（JSON格式）")
    parser.add_argument("--output", help="输出报告文件路径")

    args = parser.parse_args()

    # 加载设计选项
    if args.config:
        options = load_config(Path(args.config))
    else:
        print("未提供配置文件，使用示例数据...")
        options = load_config(Path("dummy.json"))

    # 分析PPA
    results = analyze_ppa_tradeoffs(options)

    # 生成报告
    report = generate_report(results)

    # 输出
    if args.output:
        output_path = Path(args.output)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(report, encoding="utf-8")
        print(f"报告已保存至: {output_path}")
    else:
        print(report)


if __name__ == "__main__":
    main()
