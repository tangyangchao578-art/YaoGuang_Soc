#!/usr/bin/env python3
"""
功能安全分析自动化工具
提供FMEA、FTA、FMEDA等安全分析的自动化支持
"""

import json
import csv
import argparse
import sys
from dataclasses import dataclass, asdict
from typing import List, Dict, Optional, Union
from enum import Enum

class Severity(Enum):
    """严重度等级"""
    VERY_LOW = 1
    LOW = 2
    MODERATE_LOW = 3
    MODERATE = 4
    MODERATE_HIGH = 5
    HIGH = 6
    VERY_HIGH = 7
    CRITICAL = 8
    HAZARDOUS = 9
    CATASTROPHIC = 10

class Occurrence(Enum):
    """发生频率"""
    EXTREMELY_UNLIKELY = 1
    VERY_LOW = 2
    LOW = 3
    MODERATE = 4
    MODERATE_HIGH = 5
    HIGH = 6
    VERY_HIGH = 7
    EXTREMELY_HIGH = 8
    FREQUENT = 9
    CONSTANT = 10

class Detection(Enum):
    """可检测度"""
    ALMOST_CERTAIN = 1
    VERY_HIGH = 2
    HIGH = 3
    MODERATE_HIGH = 4
    MODERATE = 5
    LOW = 6
    VERY_LOW = 7
    EXTREMELY_LOW = 8
    REMOTE = 9
    ABSOLUTE_UNCERTAINTY = 10

class ASILLevel(Enum):
    """ASIL等级"""
    QM = 0
    A = 1
    B = 2
    C = 3
    D = 4

@dataclass
class FailureMode:
    """失效模式"""
    id: str
    component: str
    function: str
    failure_mode: str
    local_effect: str
    system_effect: str
    severity: int
    cause: str
    occurrence: int
    controls: str
    detection: int
    rpn: int = 0
    recommended_actions: str = ""
    
    def calculate_rpn(self):
        """计算RPN"""
        self.rpn = self.severity * self.occurrence * self.detection
        return self.rpn

@dataclass
class SafetyRequirement:
    """安全需求"""
    id: str
    description: str
    asil_level: int
    ftti: float  # ms
    safe_state: str
    safety_mechanisms: List[str]
    verification_methods: List[str]

@dataclass
class ComponentReliability:
    """组件可靠性数据"""
    component_name: str
    component_type: str
    fit_rate: float  # FIT
    failure_modes: List[str]
    diagnostic_coverage: float
    failure_influence: str  # safe / unsafe

@dataclass
class ComplianceResult:
    """合规性结果"""
    spfm_compliant: bool
    lfm_compliant: bool
    pmhf_compliant: bool
    dc_compliant: bool
    spfm: float
    lfm: float
    pmhf: float
    avg_dc: float

class FMEAAnalyzer:
    """FMEA分析器"""
    
    def __init__(self):
        self.failure_modes: List[FailureMode] = []
    
    def add_failure_mode(self, failure_mode: FailureMode):
        """添加失效模式"""
        failure_mode.calculate_rpn()
        self.failure_modes.append(failure_mode)
    
    def calculate_rpn(self, failure_mode: FailureMode):
        """计算RPN"""
        return failure_mode.severity * failure_mode.occurrence * failure_mode.detection
    
    def prioritize(self):
        """优先级排序"""
        return sorted(self.failure_modes, key=lambda fm: fm.rpn, reverse=True)
    
    def export_to_csv(self, filename: str):
        """导出到CSV"""
        with open(filename, 'w', newline='', encoding='utf-8') as f:
            writer = csv.writer(f)
            writer.writerow([
                'ID', 'Component', 'Function', 'Failure Mode', 
                'Local Effect', 'System Effect', 'Severity',
                'Cause', 'Occurrence', 'Controls', 'Detection',
                'RPN', 'Recommended Actions'
            ])
            for fm in self.failure_modes:
                writer.writerow([
                    fm.id, fm.component, fm.function, fm.failure_mode,
                    fm.local_effect, fm.system_effect, fm.severity,
                    fm.cause, fm.occurrence, fm.controls, fm.detection,
                    fm.rpn, fm.recommended_actions
                ])
    
    def import_from_csv(self, filename: str):
        """从CSV导入"""
        with open(filename, 'r', encoding='utf-8') as f:
            reader = csv.DictReader(f)
            for row in reader:
                failure_mode = FailureMode(
                    id=row['ID'],
                    component=row['Component'],
                    function=row['Function'],
                    failure_mode=row['Failure Mode'],
                    local_effect=row['Local Effect'],
                    system_effect=row['System Effect'],
                    severity=int(row['Severity']),
                    cause=row['Cause'],
                    occurrence=int(row['Occurrence']),
                    controls=row['Controls'],
                    detection=int(row['Detection']),
                    rpn=int(row['RPN']) if row['RPN'] else 0,
                    recommended_actions=row['Recommended Actions'] if 'Recommended Actions' in row else ""
                )
                self.add_failure_mode(failure_mode)
    
    def generate_report(self, filename: str):
        """生成报告"""
        prioritized = self.prioritize()
        
        with open(filename, 'w', encoding='utf-8') as f:
            f.write("=" * 80 + "\n")
            f.write("FMEA分析报告\n")
            f.write("=" * 80 + "\n\n")
            
            f.write(f"总失效模式数: {len(prioritized)}\n\n")
            
            high_priority = [fm for fm in prioritized if fm.rpn > 200]
            f.write(f"高优先级失效模式 (RPN > 200): {len(high_priority)}\n\n")
            
            medium_priority = [fm for fm in prioritized if 100 < fm.rpn <= 200]
            f.write(f"中优先级失效模式 (100 < RPN ≤ 200): {len(medium_priority)}\n\n")
            
            low_priority = [fm for fm in prioritized if fm.rpn <= 100]
            f.write(f"低优先级失效模式 (RPN ≤ 100): {len(low_priority)}\n\n")
            
            f.write("=" * 80 + "\n")
            f.write("优先级排序\n")
            f.write("=" * 80 + "\n\n")
            
            for i, fm in enumerate(prioritized, 1):
                f.write(f"{i}. ID: {fm.id}\n")
                f.write(f"   组件: {fm.component}\n")
                f.write(f"   功能: {fm.function}\n")
                f.write(f"   失效模式: {fm.failure_mode}\n")
                f.write(f"   RPN: {fm.rpn} (S={fm.severity}, O={fm.occurrence}, D={fm.detection})\n")
                f.write(f"   建议措施: {fm.recommended_actions}\n\n")

class FMEDAAnalyzer:
    """FMEDA分析器"""
    
    def __init__(self):
        self.components: List[ComponentReliability] = []
        self.safety_requirements: List[SafetyRequirement] = []
    
    def add_component(self, component: ComponentReliability):
        """添加组件"""
        self.components.append(component)
    
    def add_safety_requirement(self, requirement: SafetyRequirement):
        """添加安全需求"""
        self.safety_requirements.append(requirement)
    
    def calculate_spfm(self) -> float:
        """计算单点故障度量（SPFM）"""
        safe_detected_fit = 0
        safe_undetected_fit = 0
        
        for comp in self.components:
            fit = comp.fit_rate
            dc = comp.diagnostic_coverage / 100.0
            
            if comp.failure_influence == "safe":
                safe_detected_fit += fit * dc
                safe_undetected_fit += fit * (1 - dc)
        
        total_fit = safe_detected_fit + safe_undetected_fit
        if total_fit == 0:
            return 100.0
        
        spfm = (1 - safe_undetected_fit / total_fit) * 100
        return spfm
    
    def calculate_lfm(self) -> float:
        """计算潜伏故障度量（LFM）"""
        latent_fit = 0
        total_fit = 0
        
        for comp in self.components:
            fit = comp.fit_rate
            total_fit += fit
            
            dc = comp.diagnostic_coverage / 100.0
            latent_fit += fit * (1 - dc)
        
        if total_fit == 0:
            return 100.0
        
        lfm = (1 - latent_fit / total_fit) * 100
        return lfm
    
    def calculate_pmhf(self) -> float:
        """计算随机硬件失效概率（PMHF）"""
        pmhf = 0
        
        for comp in self.components:
            fit = comp.fit_rate
            dc = comp.diagnostic_coverage / 100.0
            pmhf += fit * (1 - dc)
        
        return pmhf
    
    def calculate_average_dc(self) -> float:
        """计算平均诊断覆盖率"""
        if not self.components:
            return 0.0
        
        total_dc = sum(comp.diagnostic_coverage for comp in self.components)
        return total_dc / len(self.components)
    
    def evaluate_asil_compliance(self, asil_level: int) -> ComplianceResult:
        """评估ASIL合规性"""
        spfm = self.calculate_spfm()
        lfm = self.calculate_lfm()
        pmhf = self.calculate_pmhf()
        avg_dc = self.calculate_average_dc()
        
        asil_targets = {
            0: {'spfm': 0, 'lfm': 0, 'pmhf': float('inf'), 'dc': 0},
            1: {'spfm': 90, 'lfm': 60, 'pmhf': 100, 'dc': 60},
            2: {'spfm': 90, 'lfm': 60, 'pmhf': 10, 'dc': 90},
            3: {'spfm': 97, 'lfm': 80, 'pmhf': 1, 'dc': 97},
            4: {'spfm': 99, 'lfm': 90, 'pmhf': 0.1, 'dc': 99}
        }
        
        target = asil_targets.get(asil_level, asil_targets[0])
        
        return ComplianceResult(
            spfm_compliant=spfm >= target['spfm'],
            lfm_compliant=lfm >= target['lfm'],
            pmhf_compliant=pmhf <= target['pmhf'],
            dc_compliant=avg_dc >= target['dc'],
            spfm=spfm,
            lfm=lfm,
            pmhf=pmhf,
            avg_dc=avg_dc
        )
    
    def generate_report(self, filename: str, asil_level: int = 2):
        """生成报告"""
        compliance = self.evaluate_asil_compliance(asil_level)
        
        with open(filename, 'w', encoding='utf-8') as f:
            f.write("=" * 80 + "\n")
            f.write("FMEDA分析报告\n")
            f.write("=" * 80 + "\n\n")
            
            f.write(f"目标ASIL等级: ASIL{asil_level if asil_level > 0 else 'QM'}\n\n")
            
            f.write("=" * 80 + "\n")
            f.write("组件清单\n")
            f.write("=" * 80 + "\n\n")
            
            for comp in self.components:
                f.write(f"组件: {comp.component_name}\n")
                f.write(f"  类型: {comp.component_type}\n")
                f.write(f"  FIT率: {comp.fit_rate} FIT\n")
                f.write(f"  诊断覆盖率: {comp.diagnostic_coverage}%\n")
                f.write(f"  失效影响: {comp.failure_influence}\n\n")
            
            f.write("=" * 80 + "\n")
            f.write("安全指标\n")
            f.write("=" * 80 + "\n\n")
            
            f.write(f"SPFM (单点故障度量): {compliance.spfm:.2f}%\n")
            f.write(f"  合规: {'✓' if compliance.spfm_compliant else '✗'}\n\n")
            
            f.write(f"LFM (潜伏故障度量): {compliance.lfm:.2f}%\n")
            f.write(f"  合规: {'✓' if compliance.lfm_compliant else '✗'}\n\n")
            
            f.write(f"PMHF (随机硬件失效概率): {compliance.pmhf:.2f} FIT\n")
            f.write(f"  合规: {'✓' if compliance.pmhf_compliant else '✗'}\n\n")
            
            f.write(f"平均诊断覆盖率: {compliance.avg_dc:.2f}%\n")
            f.write(f"  合规: {'✓' if compliance.dc_compliant else '✗'}\n\n")
            
            f.write("=" * 80 + "\n")
            f.write("合规性总结\n")
            f.write("=" * 80 + "\n\n")
            
            all_compliant = all([
                compliance.spfm_compliant,
                compliance.lfm_compliant,
                compliance.pmhf_compliant,
                compliance.dc_compliant
            ])
            
            if all_compliant:
                f.write("✓ 所有安全指标均满足ASIL要求\n")
            else:
                f.write("✗ 部分安全指标未满足ASIL要求\n")
                f.write("  建议采取以下措施:\n")
                if not compliance.spfm_compliant:
                    f.write("  - 增加安全机制以提高SPFM\n")
                if not compliance.lfm_compliant:
                    f.write("  - 改进潜伏故障检测以提高LFM\n")
                if not compliance.pmhf_compliant:
                    f.write("  - 降低失效率或提高诊断覆盖率\n")
                if not compliance.dc_compliant:
                    f.write("  - 增加诊断机制以提高诊断覆盖率\n")

def main():
    parser = argparse.ArgumentParser(description='功能安全分析工具')
    parser.add_argument('command', choices=['fmea', 'fmeda', 'report'],
                       help='分析命令')
    parser.add_argument('--input', help='输入文件')
    parser.add_argument('--output', help='输出文件')
    parser.add_argument('--asil', type=int, choices=[0, 1, 2, 3, 4],
                       help='ASIL等级 (0=QM, 1=A, 2=B, 3=C, 4=D)', default=2)
    
    args = parser.parse_args()
    
    if args.command == 'fmea':
        analyzer = FMEAAnalyzer()
        if args.input:
            analyzer.import_from_csv(args.input)
        
        if not analyzer.failure_modes:
            analyzer.add_failure_mode(FailureMode(
                id="FM-001",
                component="CPU",
                function="计算控制",
                failure_mode="锁步不匹配",
                local_effect="计算错误",
                system_effect="车辆控制失效",
                severity=9,
                cause="硬件故障",
                occurrence=3,
                controls="锁步比较器",
                detection=2,
                recommended_actions="增加冗余和诊断"
            ))
        
        if args.output:
            analyzer.export_to_csv(args.output.replace('.csv', '_out.csv'))
            analyzer.generate_report(args.output)
        else:
            analyzer.export_to_csv("fmea_out.csv")
            analyzer.generate_report("fmea_report.txt")
    
    elif args.command == 'fmeda':
        analyzer = FMEDAAnalyzer()
        
        analyzer.add_component(ComponentReliability(
            component_name="CPU",
            component_type="处理器",
            fit_rate=10.0,
            failure_modes=["软错误", "硬错误"],
            diagnostic_coverage=95.0,
            failure_influence="unsafe"
        ))
        
        analyzer.add_component(ComponentReliability(
            component_name="SRAM",
            component_type="存储器",
            fit_rate=100.0,
            failure_modes=["位翻转", "位错误"],
            diagnostic_coverage=99.0,
            failure_influence="safe"
        ))
        
        analyzer.add_component(ComponentReliability(
            component_name="Flash",
            component_type="存储器",
            fit_rate=50.0,
            failure_modes=["位错误", "块错误"],
            diagnostic_coverage=98.0,
            failure_influence="safe"
        ))
        
        output_file = args.output if args.output else "fmeda_report.txt"
        analyzer.generate_report(output_file, args.asil)
    
    elif args.command == 'report':
        print("生成功能安全报告...")

if __name__ == '__main__':
    main()
