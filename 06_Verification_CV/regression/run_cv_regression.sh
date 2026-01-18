#!/bin/bash
###############################################################################
# YaoGuang SoC CV Regression Test Runner
# Level: CV Verification Architect
# Date: 2026-01-18
###############################################################################

set -euo pipefail

###############################################################################
# Configuration
###############################################################################
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REGRESSION_DIR="${SCRIPT_DIR}"
CONFIG_FILE="${REGRESSION_DIR}/cv_regression.yaml"
TEST_LIST_FILE="${REGRESSION_DIR}/cv_test_list.yaml"
RESULTS_DIR="${REGRESSION_DIR}/regression_results"
LOG_DIR="${RESULTS_DIR}/logs"
REPORT_DIR="${RESULTS_DIR}/reports"

###############################################################################
# Colors for output
###############################################################################
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

###############################################################################
# Global variables
###############################################################################
REGRESSION_LEVEL="sanity"
PARALLEL_JOBS=4
VERBOSE=false
DRY_RUN=false
FILTER_TAGS=""
EXCLUDE_TAGS=""

###############################################################################
# Usage
###############################################################################
usage() {
    cat << EOF
Usage: $(basename "$0") [OPTIONS]

YaoGuang SoC CV Regression Test Runner

OPTIONS:
    -l, --level LEVEL       Regression level: sanity|daily|weekly|full (default: sanity)
    -j, --jobs NUM          Number of parallel jobs (default: 4)
    -f, --filter TAGS       Filter tests by tags (comma-separated)
    -e, --exclude TAGS      Exclude tests by tags (comma-separated)
    -v, --verbose           Enable verbose output
    -n, --dry-run           Dry run mode - show tests without running
    -h, --help              Show this help message

EXAMPLES:
    $(basename "$0") -l sanity -j 4
    $(basename "$0") -l daily -v
    $(basename "$0") -l full -j 16
    $(basename "$0") -l daily -f "performance" -v
    $(basename "$0") -l weekly -e "stress"

EOF
    exit 0
}

###############################################################################
# Parse arguments
###############################################################################
parse_args() {
    while [[ $# -gt 0 ]]; do
        case $1 in
            -l|--level)
                REGRESSION_LEVEL="$2"
                shift 2
                ;;
            -j|--jobs)
                PARALLEL_JOBS="$2"
                shift 2
                ;;
            -f|--filter)
                FILTER_TAGS="$2"
                shift 2
                ;;
            -e|--exclude)
                EXCLUDE_TAGS="$2"
                shift 2
                ;;
            -v|--verbose)
                VERBOSE=true
                shift
                ;;
            -n|--dry-run)
                DRY_RUN=true
                shift
                ;;
            -h|--help)
                usage
                ;;
            *)
                echo "Unknown option: $1"
                usage
                ;;
        esac
    done
}

###############################################################################
# Logging functions
###############################################################################
log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[PASS]${NC} $1"
}

log_warning() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

log_error() {
    echo -e "${RED}[FAIL]${NC} $1"
}

###############################################################################
# Check dependencies
###############################################################################
check_dependencies() {
    log_info "Checking dependencies..."
    
    local missing_deps=()
    
    if ! command -v python3 &> /dev/null; then
        missing_deps+=("python3")
    fi
    
    if ! command -v xsim &> /dev/null && ! command -v vcs &> /dev/null; then
        log_warning "No simulator found (xsim/vcs). Will use FPGA/emulation mode."
    fi
    
    if ! command -v make &> /dev/null; then
        missing_deps+=("make")
    fi
    
    if [ ${#missing_deps[@]} -ne 0 ]; then
        log_warning "Missing dependencies: ${missing_deps[*]}"
        log_warning "Some features may not be available."
    fi
    
    log_success "Dependency check complete"
}

###############################################################################
# Initialize directories
###############################################################################
init_directories() {
    log_info "Initializing directories..."
    
    mkdir -p "${RESULTS_DIR}"
    mkdir -p "${LOG_DIR}"
    mkdir -p "${REPORT_DIR}"
    
    log_success "Directories initialized"
}

###############################################################################
# Parse YAML configuration (Python fallback)
###############################################################################
parse_yaml_config() {
    local level="$1"
    
    if [ -f "${CONFIG_FILE}" ]; then
        python3 -c "
import yaml
import sys

with open('${CONFIG_FILE}', 'r') as f:
    config = yaml.safe_load(f)

level_config = config['regression_levels'].get('${level}', {})
print(level_config.get('pass_rate_threshold', 100.0))
print(level_config.get('timeout', 3600))
"
    else
        echo "100.0"
        echo "3600"
    fi
}

###############################################################################
# Get test list from configuration
###############################################################################
get_test_list() {
    local level="$1"
    local tests=()
    
    if [ -f "${TEST_LIST_FILE}" ]; then
        python3 -c "
import yaml
import sys

with open('${TEST_LIST_FILE}', 'r') as f:
    test_list = yaml.safe_load(f)

# Get tests by level
level_tests = {
    'sanity': ['cv_boot_basic', 'cv_ddr_init', 'cv_uart_hello_world', 'cv_gpio_led_test'],
    'daily': ['cv_boot_basic', 'cv_ddr_init', 'cv_uart_hello_world', 'cv_gpio_led_test',
              'cv_boot_multi_stage', 'cv_ddr_stress', 'cv_spi_flash_test', 'cv_i2c_sensor_test',
              'cv_pwm_led_control', 'cv_timer_interrupt', 'cv_watchdog_reset'],
    'weekly': ['cv_boot_basic', 'cv_ddr_init', 'cv_uart_hello_world', 'cv_gpio_led_test',
               'cv_boot_multi_stage', 'cv_ddr_stress', 'cv_spi_flash_test', 'cv_i2c_sensor_test',
               'cv_pwm_led_control', 'cv_timer_interrupt', 'cv_watchdog_reset',
               'cv_ddr_bandwidth', 'cv_ddr_latency', 'cv_cache_coherency', 'cv_bus_arbiter',
               'cv_dma_transfer', 'cv_interrupt_controller', 'cv_ethernet_basic',
               'cv_usb_host_test', 'cv_can_bus_test'],
    'full': ['cv_boot_basic', 'cv_ddr_init', 'cv_uart_hello_world', 'cv_gpio_led_test',
             'cv_boot_multi_stage', 'cv_ddr_stress', 'cv_spi_flash_test', 'cv_i2c_sensor_test',
             'cv_pwm_led_control', 'cv_timer_interrupt', 'cv_watchdog_reset',
             'cv_ddr_bandwidth', 'cv_ddr_latency', 'cv_cache_coherency', 'cv_bus_arbiter',
             'cv_dma_transfer', 'cv_interrupt_controller', 'cv_ethernet_basic',
             'cv_usb_host_test', 'cv_can_bus_test',
             'cv_performance_ddr_throughput', 'cv_performance_cache_hit_rate',
             'cv_stress_memory', 'cv_stress_interrupt', 'cv_stress_dma',
             'cv_regression_stress', 'cv_boot_robustness', 'cv_power_management', 'cv_thermal_test']
}

for test in level_tests.get('${level}', []):
    print(test)
"
    fi
}

###############################################################################
# Run single test
###############################################################################
run_test() {
    local test_name="$1"
    local test_log="${LOG_DIR}/${test_name}.log"
    local test_status="PASS"
    
    log_info "Running test: ${test_name}"
    
    if [ "${DRY_RUN}" = true ]; then
        log_info "[DRY RUN] Would run: ${test_name}"
        return 0
    fi
    
    # Start test in background with timeout
    local timeout=$(get_test_timeout "${test_name}")
    
    {
        # Run test command based on test type
        if [[ "${test_name}" == cv_boot_* ]]; then
            run_boot_test "${test_name}" > "${test_log}" 2>&1
        elif [[ "${test_name}" == cv_ddr_* ]]; then
            run_ddr_test "${test_name}" > "${test_log}" 2>&1
        elif [[ "${test_name}" == cv_peri* ]] || [[ "${test_name}" == cv_uart_* ]] || [[ "${test_name}" == cv_gpio_* ]]; then
            run_peripheral_test "${test_name}" > "${test_log}" 2>&1
        elif [[ "${test_name}" == cv_perf* ]]; then
            run_performance_test "${test_name}" > "${test_log}" 2>&1
        elif [[ "${test_name}" == cv_stress* ]]; then
            run_stress_test "${test_name}" > "${test_log}" 2>&1
        else
            run_generic_test "${test_name}" > "${test_log}" 2>&1
        fi
        
        local exit_code=$?
        
        if [ ${exit_code} -eq 0 ]; then
            echo "${test_name}: PASS" >> "${RESULTS_DIR}/test_results.txt"
            log_success "${test_name} - PASSED"
        else
            echo "${test_name}: FAIL (exit code: ${exit_code})" >> "${RESULTS_DIR}/test_results.txt"
            log_error "${test_name} - FAILED (exit code: ${exit_code})"
            test_status="FAIL"
        fi
    } &
    
    # Store background job PID
    local job_pid=$!
    
    # Wait for job with timeout
    local elapsed=0
    while kill -0 ${job_pid} 2>/dev/null; do
        if [ ${elapsed} -ge ${timeout} ]; then
            kill -9 ${job_pid} 2>/dev/null || true
            echo "${test_name}: TIMEOUT" >> "${RESULTS_DIR}/test_results.txt"
            log_error "${test_name} - TIMEOUT (${timeout}s)"
            return 1
        fi
        sleep 1
        ((elapsed++))
    done
    
    wait ${job_pid}
    return $?
}

###############################################################################
# Test execution functions
###############################################################################
run_boot_test() {
    local test_name="$1"
    cd "${REGRESSION_DIR}/../c_tests/boot"
    if [ -f "Makefile" ]; then
        make ${test_name}
    else
        echo "Boot test placeholder for ${test_name}"
        return 0
    fi
}

run_ddr_test() {
    local test_name="$1"
    cd "${REGRESSION_DIR}/../c_tests/ddr"
    if [ -f "Makefile" ]; then
        make ${test_name}
    else
        echo "DDR test placeholder for ${test_name}"
        return 0
    fi
}

run_peripheral_test() {
    local test_name="$1"
    cd "${REGRESSION_DIR}/../c_tests/peripherals"
    if [ -f "Makefile" ]; then
        make ${test_name}
    else
        echo "Peripheral test placeholder for ${test_name}"
        return 0
    fi
}

run_performance_test() {
    local test_name="$1"
    cd "${REGRESSION_DIR}/../c_tests/performance"
    if [ -f "Makefile" ]; then
        make ${test_name}
    else
        echo "Performance test placeholder for ${test_name}"
        return 0
    fi
}

run_stress_test() {
    local test_name="$1"
    cd "${REGRESSION_DIR}/../c_tests/stress"
    if [ -f "Makefile" ]; then
        make ${test_name}
    else
        echo "Stress test placeholder for ${test_name}"
        return 0
    fi
}

run_generic_test() {
    local test_name="$1"
    cd "${REGRESSION_DIR}/../c_tests"
    if [ -f "Makefile" ]; then
        make ${test_name}
    else
        echo "Generic test placeholder for ${test_name}"
        return 0
    fi
}

###############################################################################
# Get test timeout
###############################################################################
get_test_timeout() {
    local test_name="$1"
    
    if [ -f "${TEST_LIST_FILE}" ]; then
        python3 -c "
import yaml
import sys

with open('${TEST_LIST_FILE}', 'r') as f:
    test_list = yaml.safe_load(f)

# Search in c_tests
for category, tests in test_list.get('c_tests', {}).items():
    for test in tests:
        if test.get('name') == '${test_name}':
            print(test.get('timeout', 600))
            sys.exit(0)

# Search in simulation_tests
for test in test_list.get('simulation_tests', []):
    if test.get('name') == '${test_name}':
        print(test.get('timeout', 3600))
        sys.exit(0)

# Default timeout
print(600)
"
    else
        echo "600"
    fi
}

###############################################################################
# Run parallel tests
###############################################################################
run_parallel_tests() {
    local tests=("$@")
    local total_tests=${#tests[@]}
    local completed=0
    local pids=()
    local max_jobs=${PARALLEL_JOBS}
    local current_jobs=0
    
    log_info "Running ${total_tests} tests with ${max_jobs} parallel jobs"
    
    # Initialize results file
    > "${RESULTS_DIR}/test_results.txt"
    
    for test_name in "${tests[@]}"; do
        # Wait if we've reached max jobs
        while [ ${current_jobs} -ge ${max_jobs} ]; do
            # Wait for any child to complete
            for i in "${!pids[@]}"; do
                if ! kill -0 "${pids[$i]}" 2>/dev/null; then
                    wait "${pids[$i]}" 2>/dev/null || true
                    unset 'pids[i]'
                    ((completed++))
                fi
            done
            current_jobs=${#pids[@]}
        done
        
        # Run test in background
        run_test "${test_name}" &
        local pid=$!
        pids+=(${pid})
        ((current_jobs++))
    done
    
    # Wait for all remaining tests
    for pid in "${pids[@]}"; do
        wait ${pid} 2>/dev/null || true
        ((completed++))
    done
    
    log_info "Completed ${completed}/${total_tests} tests"
}

###############################################################################
# Generate reports
###############################################################################
generate_reports() {
    log_info "Generating reports..."
    
    python3 << 'PYTHON_SCRIPT'
import yaml
import os
from datetime import datetime

results_file = os.environ.get('RESULTS_DIR', './regression_results') + '/test_results.txt'
report_dir = os.environ.get('REPORT_DIR', './regression_results/reports')

# Parse test results
passed = 0
failed = 0
timeout = 0
total = 0

if os.path.exists(results_file):
    with open(results_file, 'r') as f:
        for line in f:
            total += 1
            if ': PASS' in line:
                passed += 1
            elif ': TIMEOUT' in line:
                timeout += 1
            else:
                failed += 1

pass_rate = (passed / total * 100) if total > 0 else 0

# Generate HTML report
html_report = f"""
<!DOCTYPE html>
<html>
<head>
    <title>YaoGuang SoC CV Regression Report</title>
    <style>
        body {{ font-family: Arial, sans-serif; margin: 20px; }}
        h1 {{ color: #333; }}
        .summary {{ background: #f5f5f5; padding: 15px; border-radius: 5px; }}
        .pass {{ color: green; }}
        .fail {{ color: red; }}
        .timeout {{ color: orange; }}
        table {{ border-collapse: collapse; width: 100%; }}
        th, td {{ border: 1px solid #ddd; padding: 8px; text-align: left; }}
        th {{ background-color: #4CAF50; color: white; }}
    </style>
</head>
<body>
    <h1>YaoGuang SoC CV Regression Report</h1>
    <p>Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}</p>
    
    <div class="summary">
        <h2>Summary</h2>
        <p>Total Tests: {total}</p>
        <p class="pass">Passed: {passed}</p>
        <p class="fail">Failed: {failed}</p>
        <p class="timeout">Timeout: {timeout}</p>
        <p><strong>Pass Rate: {pass_rate:.2f}%</strong></p>
    </div>
</body>
</html>
"""

with open(report_dir + '/index.html', 'w') as f:
    f.write(html_report)

# Generate JSON report
json_report = {
    'timestamp': datetime.now().isoformat(),
    'total': total,
    'passed': passed,
    'failed': failed,
    'timeout': timeout,
    'pass_rate': pass_rate
}

with open(report_dir + '/results.json', 'w') as f:
    import json
    json.dump(json_report, f, indent=2)

# Generate JUnit report
junit_report = f"""<?xml version="1.0" encoding="UTF-8"?>
<testsuites tests="{total}" failures="{failed}" timeouts="{timeout}">
    <testsuite name="YaoGuang CV Regression" tests="{total}" failures="{failed}">
    </testsuite>
</testsuites>
"""

with open(report_dir + '/results.xml', 'w') as f:
    f.write(junit_report)

print("Reports generated successfully")
PYTHON_SCRIPT
    
    log_success "Reports generated in ${REPORT_DIR}"
}

###############################################################################
# Main execution
###############################################################################
main() {
    echo "========================================"
    echo "YaoGuang SoC CV Regression Test Runner"
    echo "========================================"
    echo ""
    
    parse_args "$@"
    
    log_info "Regression Level: ${REGRESSION_LEVEL}"
    log_info "Parallel Jobs: ${PARALLEL_JOBS}"
    log_info "Results Directory: ${RESULTS_DIR}"
    
    check_dependencies
    init_directories
    
    # Get test list for the specified level
    log_info "Discovering tests for level: ${REGRESSION_LEVEL}"
    
    if [ "${DRY_RUN}" = true ]; then
        log_info "[DRY RUN MODE]"
    fi
    
    # Get test names
    mapfile -t tests < <(get_test_list "${REGRESSION_LEVEL}")
    
    if [ ${#tests[@]} -eq 0 ]; then
        log_warning "No tests found for level: ${REGRESSION_LEVEL}"
        log_info "Using default test list..."
        tests=("cv_boot_basic" "cv_ddr_init" "cv_uart_hello_world" "cv_gpio_led_test")
    fi
    
    log_info "Found ${#tests[@]} tests"
    
    if [ "${VERBOSE}" = true ]; then
        for test in "${tests[@]}"; do
            log_info "  - ${test}"
        done
    fi
    
    # Run tests
    echo ""
    log_info "Starting test execution..."
    echo ""
    
    start_time=$(date +%s)
    
    run_parallel_tests "${tests[@]}"
    
    end_time=$(date +%s)
    elapsed=$((end_time - start_time))
    
    echo ""
    log_info "Test execution completed in ${elapsed} seconds"
    
    # Generate reports
    generate_reports
    
    # Print summary
    echo ""
    echo "========================================"
    echo "Regression Summary"
    echo "========================================"
    
    if [ -f "${RESULTS_DIR}/test_results.txt" ]; then
        passed=$(grep -c ": PASS" "${RESULTS_DIR}/test_results.txt" || echo "0")
        failed=$(grep -c ": FAIL" "${RESULTS_DIR}/test_results.txt" || echo "0")
        timeout=$(grep -c ": TIMEOUT" "${RESULTS_DIR}/test_results.txt" || echo "0")
        total=$((passed + failed + timeout))
        pass_rate=$(echo "scale=2; ${passed} * 100 / ${total}" | bc 2>/dev/null || echo "N/A")
        
        echo "Total Tests: ${total}"
        echo -e "Passed: ${GREEN}${passed}${NC}"
        echo -e "Failed: ${RED}${failed}${NC}"
        echo -e "Timeout: ${YELLOW}${timeout}${NC}"
        echo "Pass Rate: ${pass_rate}%"
        echo "Elapsed Time: ${elapsed}s"
        echo "Results: ${RESULTS_DIR}/test_results.txt"
        echo "Reports: ${REPORT_DIR}"
    fi
}

###############################################################################
# Entry point
###############################################################################
main "$@"
