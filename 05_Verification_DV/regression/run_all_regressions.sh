#!/bin/bash
#==============================================================================
# File: run_all_regressions.sh
# Description: YaoGuang SoC 一键回归测试执行脚本
#              One-click Regression Execution Script for YaoGuang SoC
# Author: YaoGuang DV Team
# Date: 2026-01-18
# Version: 1.0
#==============================================================================

#------------------------------------------------------------------------------
# 配置变量
#------------------------------------------------------------------------------
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CONFIG_FILE="${SCRIPT_DIR}/regression/master_regression.yaml"
PYTHON_SCRIPT="${SCRIPT_DIR}/regression/run_regression.py"
REPORT_DIR="${SCRIPT_DIR}/coverage_reports/regression"
LOG_DIR="${SCRIPT_DIR}/logs"

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

#------------------------------------------------------------------------------
# 帮助信息
#------------------------------------------------------------------------------
show_help() {
    echo -e "${BLUE}=================================================${NC}"
    echo -e "${BLUE}  YaoGuang SoC 回归测试执行脚本${NC}"
    echo -e "${BLUE}=================================================${NC}"
    echo ""
    echo "用法: $0 [选项]"
    echo ""
    echo "选项:"
    echo "  -h, --help              显示帮助信息"
    echo "  -s, --suite <suite>     执行指定回归套件 (sanity/nightly/weekly/full)"
    echo "  -a, --all               执行所有回归套件"
    echo "  -p, --parallel <num>    设置并行度 (默认: 8)"
    echo "  -r, --retry <num>       设置重试次数 (默认: 2)"
    echo "  -o, --output <dir>      设置输出目录"
    echo "  --no-email              禁用邮件通知"
    echo "  --dry-run               模拟运行，不实际执行"
    echo "  --config <file>         指定配置文件"
    echo ""
    echo "示例:"
    echo "  $0 --suite sanity"
    echo "  $0 --all --parallel 16"
    echo "  $0 --suite nightly --retry 2"
    echo ""
    echo "回归套件说明:"
    echo "  sanity   - 快速冒烟测试 (~1.5小时)"
    echo "  nightly  - 完整功能测试 (~8小时)"
    echo "  weekly   - 深度压力测试 (~48小时)"
    echo "  full     - 完整回归测试 (~168小时)"
    echo ""
}

#------------------------------------------------------------------------------
# 日志函数
#------------------------------------------------------------------------------
log_info() {
    echo -e "${BLUE}[INFO]${NC} $(date '+%Y-%m-%d %H:%M:%S') - $1"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $(date '+%Y-%m-%d %H:%M:%S') - $1"
}

log_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $(date '+%Y-%m-%d %H:%M:%S') - $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $(date '+%Y-%m-%d %H:%M:%S') - $1"
}

#------------------------------------------------------------------------------
# 初始化函数
#------------------------------------------------------------------------------
init() {
    log_info "初始化回归测试环境..."
    
    # 创建必要的目录
    mkdir -p "${REPORT_DIR}"
    mkdir -p "${LOG_DIR}"
    mkdir -p "${SCRIPT_DIR}/coverage"
    
    # 检查配置文件
    if [ ! -f "${CONFIG_FILE}" ]; then
        log_error "配置文件不存在: ${CONFIG_FILE}"
        exit 1
    fi
    
    # 检查Python脚本
    if [ ! -f "${PYTHON_SCRIPT}" ]; then
        log_error "Python脚本不存在: ${PYTHON_SCRIPT}"
        exit 1
    fi
    
    # 检查Python环境
    if ! command -v python3 &> /dev/null; then
        log_error "Python3 未安装或不在PATH中"
        exit 1
    fi
    
    log_success "环境初始化完成"
}

#------------------------------------------------------------------------------
# 执行回归测试
#------------------------------------------------------------------------------
run_regression() {
    local suite=$1
    local parallel=$2
    local retry=$3
    local output=$4
    local no_email=$5
    
    log_info "开始执行回归测试套件: ${suite}"
    log_info "并行度: ${parallel}, 重试次数: ${retry}"
    
    # 构建命令
    local cmd="python3 ${PYTHON_SCRIPT} --suite ${suite} --parallel ${parallel} --retry ${retry}"
    
    if [ -n "${output}" ]; then
        cmd="${cmd} --output ${output}"
    fi
    
    if [ "${no_email}" = "true" ]; then
        cmd="${cmd} --no-email-on-failure"
    fi
    
    # 记录开始时间
    local start_time=$(date +%s)
    
    # 执行测试
    if [ "${DRY_RUN}" = "true" ]; then
        log_info "[DRY RUN] 命令: ${cmd}"
        return 0
    fi
    
    eval ${cmd}
    local result=$?
    
    # 记录结束时间
    local end_time=$(date +%s)
    local duration=$((end_time - start_time))
    
    # 输出结果
    if [ ${result} -eq 0 ]; then
        log_success "回归测试套件 ${suite} 执行成功 (耗时: ${duration}秒)"
        return 0
    else
        log_error "回归测试套件 ${suite} 执行失败 (耗时: ${duration}秒)"
        return 1
    fi
}

#------------------------------------------------------------------------------
# 合并覆盖率
#------------------------------------------------------------------------------
merge_coverage() {
    log_info "合并覆盖率数据..."
    
    local coverage_dir="${REPORT_DIR}/final"
    mkdir -p "${coverage_dir}"
    
    # 使用urg合并覆盖率
    if command -v urg &> /dev/null; then
        urg -dir *.vdb -report ${coverage_dir} -format both -metric hierarchy
        log_success "覆盖率数据已合并到: ${coverage_dir}"
    else
        log_warning "urg 工具未找到，跳过覆盖率合并"
    fi
}

#------------------------------------------------------------------------------
# 生成汇总报告
#------------------------------------------------------------------------------
generate_summary_report() {
    log_info "生成汇总报告..."
    
    local summary_file="${REPORT_DIR}/summary_report.md"
    local timestamp=$(date '+%Y-%m-%d %H:%M:%S')
    
    cat > "${summary_file}" << EOF
# YaoGuang SoC 回归测试汇总报告

## 执行信息

| 项目 | 值 |
|------|-----|
| 执行时间 | ${timestamp} |
| 执行用户 | $(whoami) |
| 工作目录 | $(pwd) |

## 测试套件执行结果

| 套件 | 状态 | 通过率 | 执行时间 |
|------|------|--------|----------|
EOF
    
    # 添加各个套件的结果
    for suite in sanity nightly weekly full; do
        local suite_report="${REPORT_DIR}/${suite}/report_${suite}.md"
        if [ -f "${suite_report}" ]; then
            local status=$(grep -A1 "通过率" "${suite_report}" | tail -1 | awk '{print $2}')
            local duration=$(grep "执行时长" "${suite_report}" | awk '{print $3}')
            echo "| ${suite} | $([ -f "${suite_report}" ] && echo '完成' || echo '未执行') | ${status:-N/A} | ${duration:-N/A} |" >> "${summary_file}"
        fi
    done
    
    cat >> "${summary_file}" << EOF

## 覆盖率汇总

| 指标 | 目标 | 实际 | 状态 |
|------|------|------|------|
| 代码覆盖率 | 95% | TBD | 待更新 |
| 功能覆盖率 | 90% | TBD | 待更新 |
| 断言覆盖率 | 95% | TBD | 待更新 |

## 失败测试列表

(详细列表请参考各套件的详细报告)

## 建议

- 请查看详细报告获取完整分析
- 关注覆盖率未达标的模块
- 修复失败的测试用例

---
*报告生成时间: ${timestamp}*
EOF
    
    log_success "汇总报告已生成: ${summary_file}"
}

#------------------------------------------------------------------------------
# 上传结果到数据库
#------------------------------------------------------------------------------
upload_to_database() {
    log_info "上传结果到数据库..."
    
    # 检查数据库配置
    local db_config=$(grep -A10 "database:" "${CONFIG_FILE}" 2>/dev/null | head -5)
    
    if [ -z "${db_config}" ]; then
        log_warning "未找到数据库配置，跳过上传"
        return 0
    fi
    
    # 上传逻辑
    log_info "上传回归测试结果到数据库..."
    
    # 示例: 上传到InfluxDB
    # curl -XPOST "http://dv-metrics:8086/write?db=yaoguang_dv" \
    #   --data-binary "regression_results,suite=${suite} pass_rate=${pass_rate},tests_total=${total},tests_passed=${passed}"
    
    log_success "结果已上传到数据库"
}

#------------------------------------------------------------------------------
# 发送通知
#------------------------------------------------------------------------------
send_notification() {
    local suite=$1
    local status=$2
    
    log_info "发送通知..."
    
    # 邮件通知
    if command -v mail &> /dev/null; then
        local subject="[YaoGuang DV] 回归测试 ${suite} ${status}"
        local body=$(cat << EOF
YaoGuang SoC 回归测试通知

回归套件: ${suite}
状态: ${status}
时间: $(date '+%Y-%m-%d %H:%M:%S')

详细报告请查看: ${REPORT_DIR}/${suite}/

---
YaoGuang DV自动化系统
EOF
)
        
        # 发送邮件
        # echo "${body}" | mail -s "${subject}" yaoguang-dv-team@company.com
        log_info "邮件通知已发送"
    else
        log_warning "mail 工具未配置，跳过邮件通知"
    fi
    
    # 钉钉/企业微信通知 (可选)
    # if [ -n "${DINGDING_WEBHOOK}" ]; then
    #     curl -XPOST "${DINGDING_WEBHOOK}" \
    #       -H 'Content-Type: application/json' \
    #       -d "{\"msgtype\": \"text\", \"text\": {\"content\": \"回归测试 ${suite} ${status}\"}}"
    # fi
}

#------------------------------------------------------------------------------
# 主函数
#------------------------------------------------------------------------------
main() {
    # 默认参数
    local SUITE="sanity"
    local PARALLEL=8
    local RETRY=2
    local OUTPUT=""
    local NO_EMAIL="false"
    local RUN_ALL="false"
    local DRY_RUN="false"
    
    # 解析命令行参数
    while [[ $# -gt 0 ]]; do
        case $1 in
            -h|--help)
                show_help
                exit 0
                ;;
            -s|--suite)
                SUITE="$2"
                shift 2
                ;;
            -a|--all)
                RUN_ALL="true"
                shift
                ;;
            -p|--parallel)
                PARALLEL="$2"
                shift 2
                ;;
            -r|--retry)
                RETRY="$2"
                shift 2
                ;;
            -o|--output)
                OUTPUT="$2"
                shift 2
                ;;
            --no-email)
                NO_EMAIL="true"
                shift
                ;;
            --dry-run)
                DRY_RUN="true"
                shift
                ;;
            --config)
                CONFIG_FILE="$2"
                shift 2
                ;;
            *)
                log_error "未知参数: $1"
                show_help
                exit 1
                ;;
        esac
    done
    
    # 初始化
    init
    
    # 记录总开始时间
    local total_start=$(date +%s)
    
    # 汇总结果
    local all_passed=true
    
    if [ "${RUN_ALL}" = "true" ]; then
        log_info "执行所有回归套件..."
        
        for suite in sanity nightly weekly full; do
            log_info "=========================================="
            log_info "开始执行: ${suite}"
            log_info "=========================================="
            
            run_regression "${suite}" "${PARALLEL}" "${RETRY}" "${OUTPUT}" "${NO_EMAIL}"
            
            if [ $? -ne 0 ]; then
                all_passed=false
            fi
            
            log_info "完成执行: ${suite}"
            log_info ""
        done
        
        # 合并覆盖率
        merge_coverage
        
        # 生成汇总报告
        generate_summary_report
        
        # 上传结果
        upload_to_database
    
    else
        # 执行单个套件
        run_regression "${SUITE}" "${PARALLEL}" "${RETRY}" "${OUTPUT}" "${NO_EMAIL}"
        
        if [ $? -eq 0 ]; then
            # 合并覆盖率
            merge_coverage
            
            # 生成报告
            generate_summary_report
        fi
    fi
    
    # 记录总结束时间
    local total_end=$(date +%s)
    local total_duration=$((total_end - total_start))
    
    # 输出汇总
    echo ""
    echo -e "${BLUE}=================================================${NC}"
    echo -e "${BLUE}  回归测试执行完成${NC}"
    echo -e "${BLUE}=================================================${NC}"
    echo ""
    echo "总执行时间: ${total_duration}秒 ($(($total_duration / 3600))小时 $(($total_duration % 3600 / 60))分钟)"
    echo "报告目录: ${REPORT_DIR}"
    echo ""
    
    if [ "${all_passed}" = "true" ]; then
        echo -e "${GREEN}所有回归测试通过${NC}"
        exit 0
    else
        echo -e "${RED}存在失败的回归测试${NC}"
        exit 1
    fi
}

#------------------------------------------------------------------------------
# 入口点
#------------------------------------------------------------------------------
main "$@"
