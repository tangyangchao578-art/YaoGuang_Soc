#!/usr/bin/env python3
"""
芯片产品管理自动化工具
提供市场分析、竞品分析、产品规划、项目管理等自动化支持
"""

import json
import csv
import argparse
import sys
from dataclasses import dataclass, asdict
from typing import List, Dict, Optional, Tuple
from enum import Enum
from datetime import datetime, timedelta

class Priority(Enum):
    """优先级"""
    CRITICAL = 1
    HIGH = 2
    MEDIUM = 3
    LOW = 4

class Status(Enum):
    """状态"""
    PLANNED = 1
    IN_PROGRESS = 2
    COMPLETED = 3
    CANCELLED = 4

class LifecycleStage(Enum):
    """生命周期阶段"""
    INTRODUCTION = 1
    GROWTH = 2
    MATURITY = 3
    DECLINE = 4

@dataclass
class Competitor:
    """竞争对手"""
    name: str
    product_name: str
    performance: float  # 性能得分
    power: float  # 功耗（W）
    cost: float  # 成本（$）
    functionality: float  # 功能得分
    reliability: float  # 可靠性得分
    ecosystem: float  # 生态得分
    
    def calculate_competitiveness(self) -> float:
        """计算竞争力得分"""
        weights = {
            'performance': 0.25,
            'power': -0.20,
            'cost': -0.15,
            'functionality': 0.15,
            'reliability': 0.10,
            'ecosystem': 0.10
        }
        
        # 归一化功耗和成本（越低越好）
        normalized_power = min(self.power, 15) / 15
        normalized_cost = min(self.cost, 200) / 200
        
        score = (
            self.performance * weights['performance'] +
            (1 - normalized_power) * weights['power'] +
            (1 - normalized_cost) * weights['cost'] +
            self.functionality * weights['functionality'] +
            self.reliability * weights['reliability'] +
            self.ecosystem * weights['ecosystem']
        )
        
        return score * 100

@dataclass
class Requirement:
    """产品需求"""
    id: str
    title: str
    description: str
    priority: str  # CRITICAL, HIGH, MEDIUM, LOW
    category: str  # MUST_HAVE, SHOULD_HAVE, COULD_HAVE, WONT_HAVE
    status: str  # PLANNED, IN_PROGRESS, COMPLETED, CANCELLED
    estimated_effort: int  # 人天
    actual_effort: int = 0
    assignee: str = ""
    due_date: str = ""
    
    def get_priority_value(self) -> int:
        """获取优先级数值"""
        priority_map = {
            'CRITICAL': 1,
            'HIGH': 2,
            'MEDIUM': 3,
            'LOW': 4
        }
        return priority_map.get(self.priority, 3)

@dataclass
class Milestone:
    """里程碑"""
    id: str
    name: str
    description: str
    target_date: str
    actual_date: str = ""
    status: str = "PLANNED"  # PLANNED, IN_PROGRESS, COMPLETED, DELAYED
    deliverables: Optional[List[str]] = None
    owner: str = ""
    
    def get_deliverables(self) -> List[str]:
        return self.deliverables if self.deliverables else []
    
    def get_deliverables(self) -> List[str]:
        return self.deliverables if self.deliverables else []

@dataclass
class MarketAnalysis:
    """市场分析"""
    tam: float  # Total Addressable Market
    sam: float  # Serviceable Addressable Market
    som: float  # Serviceable Obtainable Market
    market_growth_rate: float
    target_market_share: float

class CompetitorAnalyzer:
    """竞品分析器"""
    
    def __init__(self):
        self.competitors: List[Competitor] = []
    
    def add_competitor(self, competitor: Competitor):
        """添加竞争对手"""
        self.competitors.append(competitor)
    
    def analyze(self) -> Dict:
        """分析竞品"""
        if not self.competitors:
            return {}
        
        results = {}
        for comp in self.competitors:
            results[comp.name] = {
                'competitiveness': comp.calculate_competitiveness(),
                'performance': comp.performance,
                'power': comp.power,
                'cost': comp.cost,
                'functionality': comp.functionality,
                'reliability': comp.reliability,
                'ecosystem': comp.ecosystem
            }
        
        return results
    
    def export_to_csv(self, filename: str):
        """导出到CSV"""
        with open(filename, 'w', newline='', encoding='utf-8') as f:
            writer = csv.writer(f)
            writer.writerow([
                'Name', 'Product', 'Performance', 'Power (W)', 
                'Cost ($)', 'Functionality', 'Reliability', 
                'Ecosystem', 'Competitiveness Score'
            ])
            
            for comp in self.competitors:
                writer.writerow([
                    comp.name, comp.product_name, comp.performance,
                    comp.power, comp.cost, comp.functionality,
                    comp.reliability, comp.ecosystem,
                    f"{comp.calculate_competitiveness():.2f}"
                ])
    
    def generate_report(self, filename: str):
        """生成竞品分析报告"""
        analysis = self.analyze()
        
        with open(filename, 'w', encoding='utf-8') as f:
            f.write("=" * 80 + "\n")
            f.write("竞品分析报告\n")
            f.write("=" * 80 + "\n\n")
            
            f.write(f"竞品数量: {len(self.competitors)}\n\n")
            
            # 排序
            sorted_comps = sorted(
                self.competitors, 
                key=lambda c: c.calculate_competitiveness(), 
                reverse=True
            )
            
            f.write("=" * 80 + "\n")
            f.write("竞争力排名\n")
            f.write("=" * 80 + "\n\n")
            
            for i, comp in enumerate(sorted_comps, 1):
                score = comp.calculate_competitiveness()
                f.write(f"{i}. {comp.name} - {comp.product_name}\n")
                f.write(f"   竞争力得分: {score:.2f}\n")
                f.write(f"   性能: {comp.performance}\n")
                f.write(f"   功耗: {comp.power}W\n")
                f.write(f"   成本: ${comp.cost}\n")
                f.write(f"   功能: {comp.functionality}\n")
                f.write(f"   可靠性: {comp.reliability}\n")
                f.write(f"   生态: {comp.ecosystem}\n\n")

class ProductManager:
    """产品管理器"""
    
    def __init__(self):
        self.requirements: List[Requirement] = []
        self.milestones: List[Milestone] = []
    
    def add_requirement(self, requirement: Requirement):
        """添加需求"""
        self.requirements.append(requirement)
    
    def add_milestone(self, milestone: Milestone):
        """添加里程碑"""
        self.milestones.append(milestone)
    
    def prioritize_requirements(self) -> List[Requirement]:
        """优先级排序需求"""
        return sorted(self.requirements, key=lambda r: r.get_priority_value())
    
    def calculate_total_effort(self) -> int:
        """计算总工作量"""
        return sum(req.estimated_effort for req in self.requirements)
    
    def calculate_progress(self) -> float:
        """计算进度"""
        if not self.requirements:
            return 0.0
        
        total = len(self.requirements)
        completed = sum(1 for req in self.requirements if req.status == "COMPLETED")
        return (completed / total) * 100
    
    def get_milestone_status(self) -> Dict[str, int]:
        """获取里程碑状态"""
        status_count = {}
        for ms in self.milestones:
            status_count[ms.status] = status_count.get(ms.status, 0) + 1
        return status_count
    
    def export_requirements_to_csv(self, filename: str):
        """导出需求到CSV"""
        with open(filename, 'w', newline='', encoding='utf-8') as f:
            writer = csv.writer(f)
            writer.writerow([
                'ID', 'Title', 'Description', 'Priority', 'Category',
                'Status', 'Estimated Effort', 'Actual Effort', 
                'Assignee', 'Due Date'
            ])
            
            for req in self.requirements:
                writer.writerow([
                    req.id, req.title, req.description, 
                    req.priority, req.category, req.status,
                    req.estimated_effort, req.actual_effort,
                    req.assignee, req.due_date
                ])
    
    def generate_product_report(self, filename: str):
        """生成产品报告"""
        with open(filename, 'w', encoding='utf-8') as f:
            f.write("=" * 80 + "\n")
            f.write("产品管理报告\n")
            f.write("=" * 80 + "\n\n")
            
            # 需求统计
            f.write("=" * 80 + "\n")
            f.write("需求统计\n")
            f.write("=" * 80 + "\n\n")
            
            f.write(f"总需求数: {len(self.requirements)}\n")
            f.write(f"总工作量: {self.calculate_total_effort()} 人天\n")
            f.write(f"完成进度: {self.calculate_progress():.2f}%\n\n")
            
            # 优先级分布
            priority_dist = {}
            for req in self.requirements:
                priority_dist[req.priority] = priority_dist.get(req.priority, 0) + 1
            
            f.write("优先级分布:\n")
            for priority, count in priority_dist.items():
                f.write(f"  {priority}: {count}\n")
            
            # 状态分布
            status_dist = {}
            for req in self.requirements:
                status_dist[req.status] = status_dist.get(req.status, 0) + 1
            
            f.write("\n状态分布:\n")
            for status, count in status_dist.items():
                f.write(f"  {status}: {count}\n")
            
            # 里程碑统计
            f.write("\n" + "=" * 80 + "\n")
            f.write("里程碑统计\n")
            f.write("=" * 80 + "\n\n")
            
            ms_status = self.get_milestone_status()
            for status, count in ms_status.items():
                f.write(f"{status}: {count}\n")

class MarketCalculator:
    """市场计算器"""
    
    @staticmethod
    def calculate_tam(target_customers: int, unit_demand: float, avg_price: float) -> float:
        """计算总可寻址市场（TAM）"""
        return target_customers * unit_demand * avg_price
    
    @staticmethod
    def calculate_sam(tam: float, geo_coverage: float, product_coverage: float) -> float:
        """计算可服务市场（SAM）"""
        return tam * geo_coverage * product_coverage
    
    @staticmethod
    def calculate_som(sam: float, market_share_target: float) -> float:
        """计算可获得市场（SOM）"""
        return sam * market_share_target
    
    @staticmethod
    def generate_market_report(
        target_customers: int,
        unit_demand: float,
        avg_price: float,
        geo_coverage: float,
        product_coverage: float,
        market_share_target: float,
        market_growth_rate: float
    ) -> MarketAnalysis:
        """生成市场分析报告"""
        tam = MarketCalculator.calculate_tam(target_customers, unit_demand, avg_price)
        sam = MarketCalculator.calculate_sam(tam, geo_coverage, product_coverage)
        som = MarketCalculator.calculate_som(sam, market_share_target)
        
        return MarketAnalysis(
            tam=tam,
            sam=sam,
            som=som,
            market_growth_rate=market_growth_rate,
            target_market_share=market_share_target
        )

def main():
    parser = argparse.ArgumentParser(description='芯片产品管理工具')
    parser.add_argument('command', choices=['analyze', 'report', 'market'],
                       help='管理命令')
    parser.add_argument('--input', help='输入文件')
    parser.add_argument('--output', help='输出文件')
    parser.add_argument('--customers', type=int, help='目标客户数')
    parser.add_argument('--unit-demand', type=float, help='单位需求量')
    parser.add_argument('--price', type=float, help='平均单价')
    parser.add_argument('--geo-coverage', type=float, help='地域覆盖比例 (0-1)')
    parser.add_argument('--product-coverage', type=float, help='产品线覆盖比例 (0-1)')
    parser.add_argument('--market-share', type=float, help='目标市场份额 (0-1)')
    parser.add_argument('--growth-rate', type=float, help='市场增长率 (0-1)')
    
    args = parser.parse_args()
    
    if args.command == 'analyze':
        analyzer = CompetitorAnalyzer()
        
        # 示例竞品
        analyzer.add_competitor(Competitor(
            name="Competitor A",
            product_name="Product X",
            performance=80,
            power=10,
            cost=100,
            functionality=85,
            reliability=90,
            ecosystem=75
        ))
        
        analyzer.add_competitor(Competitor(
            name="Competitor B",
            product_name="Product Y",
            performance=75,
            power=8,
            cost=80,
            functionality=80,
            reliability=85,
            ecosystem=70
        ))
        
        analyzer.add_competitor(Competitor(
            name="Competitor C",
            product_name="Product Z",
            performance=90,
            power=12,
            cost=120,
            functionality=95,
            reliability=95,
            ecosystem=80
        ))
        
        output_csv = args.output if args.output else "competitor_analysis.csv"
        output_report = args.output.replace('.csv', '_report.txt') if args.output else "competitor_report.txt"
        
        analyzer.export_to_csv(output_csv)
        analyzer.generate_report(output_report)
        print(f"竞品分析报告已生成: {output_report}")
    
    elif args.command == 'report':
        manager = ProductManager()
        
        # 示例需求
        manager.add_requirement(Requirement(
            id="REQ-001",
            title="高性能AI加速",
            description="支持深度学习推理加速",
            priority="CRITICAL",
            category="MUST_HAVE",
            status="IN_PROGRESS",
            estimated_effort=30
        ))
        
        manager.add_requirement(Requirement(
            id="REQ-002",
            title="低功耗设计",
            description="功耗小于10W",
            priority="HIGH",
            category="MUST_HAVE",
            status="PLANNED",
            estimated_effort=20
        ))
        
        manager.add_requirement(Requirement(
            id="REQ-003",
            title="多接口支持",
            description="支持PCIe、Ethernet等接口",
            priority="MEDIUM",
            category="SHOULD_HAVE",
            status="PLANNED",
            estimated_effort=15
        ))
        
        output_csv = args.output if args.output else "requirements.csv"
        output_report = args.output.replace('.csv', '_report.txt') if args.output else "product_report.txt"
        
        manager.export_requirements_to_csv(output_csv)
        manager.generate_product_report(output_report)
        print(f"产品管理报告已生成: {output_report}")
    
    elif args.command == 'market':
        if not all([
            args.customers, args.unit_demand, args.price,
            args.geo_coverage, args.product_coverage, args.market_share, args.growth_rate
        ]):
            print("错误: 市场分析需要所有参数")
            sys.exit(1)
        
        analysis = MarketCalculator.generate_market_report(
            target_customers=args.customers,
            unit_demand=args.unit_demand,
            avg_price=args.price,
            geo_coverage=args.geo_coverage,
            product_coverage=args.product_coverage,
            market_share_target=args.market_share,
            market_growth_rate=args.growth_rate
        )
        
        output_file = args.output if args.output else "market_analysis.txt"
        
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write("=" * 80 + "\n")
            f.write("市场分析报告\n")
            f.write("=" * 80 + "\n\n")
            
            f.write(f"总可寻址市场 (TAM): ${analysis.tam:,.0f}\n")
            f.write(f"可服务市场 (SAM): ${analysis.sam:,.0f}\n")
            f.write(f"可获得市场 (SOM): ${analysis.som:,.0f}\n\n")
            
            f.write(f"目标市场份额: {analysis.target_market_share * 100:.1f}%\n")
            f.write(f"市场增长率: {analysis.market_growth_rate * 100:.1f}%\n\n")
            
            # 未来5年预测
            f.write("=" * 80 + "\n")
            f.write("市场预测（未来5年）\n")
            f.write("=" * 80 + "\n\n")
            
            som = analysis.som
            for year in range(1, 6):
                som = som * (1 + analysis.market_growth_rate)
                f.write(f"Year +{year}: ${som:,.0f}\n")
        
        print(f"市场分析报告已生成: {output_file}")

if __name__ == '__main__':
    main()
