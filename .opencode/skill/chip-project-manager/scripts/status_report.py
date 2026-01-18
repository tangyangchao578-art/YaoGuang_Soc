#!/usr/bin/env python3
"""
项目状态报告生成器

生成芯片项目的周报或月报，包含完成工作、下周计划、风险和里程碑进度。

使用方法：
    python status_report.py --project <项目名称> --period week|month

示例：
    python status_report.py --project AI-Chip --period week
"""

import argparse
from pathlib import Path
from datetime import datetime


def generate_status_report(project_name: str, period: str) -> str:
    """
    生成项目状态报告模板。

    参数：
        project_name: 项目名称
        period: 报告周期 (week 或 month)

    返回：
        报告内容字符串
    """
    date_str = datetime.now().strftime("%Y-%m-%d")
    period_cn = "周报" if period == "week" else "月报"

    report = f"""# {project_name} 项目{period_cn}
## 报告日期: {date_str}

---

## 1. 本周期完成工作

### 1.1 设计相关
- [ ] 架构设计评审完成
- [ ] RTL代码编写进度
- [ ] 综合结果分析
- [ ] IP集成状态

### 1.2 验证相关
- [ ] 功能仿真测试用例
- [ ] 回归测试结果
- [ ] 时序收敛情况
- [ ] 形式验证报告

### 1.3 其他
- [ ] 文档更新
- [ ] 会议和沟通
- [ ] 外部依赖跟进

---

## 2. 下周期计划

### 2.1 设计任务
- [ ] 任务1
- [ ] 任务2

### 2.2 验证任务
- [ ] 验证计划
- [ ] 测试用例开发

---

## 3. 风险和问题

| 风险ID | 描述 | 概率 | 影响 | 状态 |
|---------|------|--------|------|------|
| R-001   | IP交付延期 | 中 | 高 | 跟踪中 |
| R-002   | 工艺偏差风险 | 低 | 中 | 监控 |
|         |      |    |    |      |

---

## 4. 里程碑进度

| 里程碑 | 计划日期 | 实际日期 | 状态 |
|--------|----------|----------|------|
| M1: 架构冻结 | 2024-01-15 | - | 进行中 |
| M2: RTL冻结 | 2024-03-15 | - | 未开始 |
| M3: 交付样片 | 2024-06-30 | - | 未开始 |

---

## 5. 资源需求

- [ ] 人力: 需要X名验证工程师
- [ ] 工具: EDA license需求
- [ ] 外部: 第三方IP支持
- [ ] 设备: FPGA平台

---

## 6. 其他事项

*待补充*

---
*本报告由 chip-project-manager skill 生成*
"""
    return report


def main():
    parser = argparse.ArgumentParser(
        description="生成芯片项目状态报告",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--project", required=True, help="项目名称")
    parser.add_argument("--period", choices=["week", "month"], default="week", help="报告周期")
    parser.add_argument("--output", help="输出文件路径（默认打印到终端）")

    args = parser.parse_args()

    report = generate_status_report(args.project, args.period)

    if args.output:
        output_path = Path(args.output)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(report, encoding="utf-8")
        print(f"报告已保存至: {output_path}")
    else:
        print(report)


if __name__ == "__main__":
    main()
