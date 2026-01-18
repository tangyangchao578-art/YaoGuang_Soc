#!/bin/bash
# YaoGuang SoC DV Simulation Runner

set -e

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

# 路径定义
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DV_DIR="$(dirname "$SCRIPT_DIR")"
ROOT_DIR="$(dirname "$DV_DIR")"

# 默认配置
SIMULATOR=${SIMULATOR:-vcs}
TEST_NAME=${TEST_NAME:-"test_basic"}
SEED=${SEED:-"random"}
WAVE=${WAVE:-0}
COVERAGE=${COVERAGE:-1}

# 打印函数
print_info() {
    echo -e "${GREEN}[INFO]${NC} $1"
}

print_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# 帮助信息
show_help() {
    echo "YaoGuang SoC DV Simulation Runner"
    echo ""
    echo "Usage: $0 <command> [options]"
    echo ""
    echo "Commands:"
    echo "  compile     Compile the verification environment"
    echo "  run         Run a single test"
    echo "  regression  Run regression tests"
    echo "  coverage    Collect and report coverage"
    echo ""
    echo "Options:"
    echo "  -t, --test <name>     Test name (default: test_basic)"
    echo "  -s, --seed <seed>     Random seed (default: random)"
    echo "  -w, --wave            Enable wave dump"
    echo "  -c, --coverage        Enable coverage collection"
    echo "  -r, --regression <name>  Regression name (default: nightly)"
    echo "  -h, --help            Show this help"
    echo ""
    echo "Environment variables:"
    echo "  SIMULATOR             Simulator to use (vcs/xcelium/questa)"
    echo "  UVM_HOME              UVM library path"
}

# 编译函数
do_compile() {
    print_info "Compiling verification environment..."

    # 确定仿真器
    case $SIMULATOR in
        vcs)
            COMPILE_CMD="vcs -full64 -sverilog"
            ;;
        xcelium)
            COMPILE_CMD="xrun -64bit -sv"
            ;;
        *)
            print_error "Unknown simulator: $SIMULATOR"
            exit 1
            ;;
    esac

    # 添加编译选项
    COMPILE_CMD="$COMPILE_CMD -f $DV_DIR/uvm_env/filelist/uvm.f"
    COMPILE_CMD="$COMPILE_CMD -top top_tb"
    COMPILE_CMD="$COMPILE_CMD +vcs+lic_wait"

    if [ $COVERAGE -eq 1 ]; then
        COMPILE_CMD="$COMPILE_CMD -cm line+branch+cond+fsm+toggle"
    fi

    echo $COMPILE_CMD
    eval $COMPILE_CMD

    print_info "Compilation completed"
}

# 运行测试函数
do_run() {
    print_info "Running test: $TEST_NAME"

    # 确定仿真器
    case $SIMULATOR in
        vcs)
            RUN_CMD="simv"
            ;;
        xcelium)
            RUN_CMD="xrun -R"
            ;;
        *)
            print_error "Unknown simulator: $SIMULATOR"
            exit 1
            ;;
    esac

    # 添加运行选项
    RUN_CMD="$RUN_CMD +UVM_TESTNAME=$TEST_NAME"

    if [ "$SEED" != "random" ]; then
        RUN_CMD="$RUN_CMD +ntb_random_seed=$SEED"
    fi

    if [ $WAVE -eq 1 ]; then
        RUN_CMD="$RUN_CMD +vcdplusfile=wave.vpd +vcdpluson"
    fi

    if [ $COVERAGE -eq 1 ]; then
        RUN_CMD="$RUN_CMD -cm line+branch+cond+fsm+toggle"
    fi

    eval $RUN_CMD

    if [ $? -eq 0 ]; then
        print_info "Test passed: $TEST_NAME"
    else
        print_error "Test failed: $TEST_NAME"
        exit 1
    fi
}

# 回归测试函数
do_regression() {
    print_info "Running regression: $REGRESSION"

    REGRESSION_FILE="$DV_DIR/regression/${REGRESSION}_list.yaml"

    if [ ! -f "$REGRESSION_FILE" ]; then
        print_error "Regression file not found: $REGRESSION_FILE"
        exit 1
    fi

    # 解析回归测试列表
    TOTAL_TESTS=0
    PASSED_TESTS=0
    FAILED_TESTS=0

    # 读取测试列表 (简单实现，实际应该用 Python/YAML 解析)
    while IFS= read -r line; do
        if [[ ! $line =~ ^# ]] && [[ ! -z $line ]]; then
            TEST_NAME=$(echo $line | awk '{print $1}')
            TOTAL_TESTS=$((TOTAL_TESTS + 1))

            print_info "Running: $TEST_NAME"
            if do_run_test $TEST_NAME; then
                PASSED_TESTS=$((PASSED_TESTS + 1))
            else
                FAILED_TESTS=$((FAILED_TESTS + 1))
            fi
        fi
    done < $REGRESSION_FILE

    print_info "Regression completed"
    print_info "Total: $TOTAL_TESTS, Passed: $PASSED_TESTS, Failed: $FAILED_TESTS"

    if [ $FAILED_TESTS -gt 0 ]; then
        exit 1
    fi
}

# 覆盖率收集函数
do_coverage() {
    print_info "Collecting coverage..."

    case $SIMULATOR in
        vcs)
            URG_CMD="urg -dir *.vdb -report coverage_report"
            ;;
        xcelium)
            ICM_CMD="imc -load all_tests.vdb -report -html"
            ;;
    esac

    eval $URG_CMD

    print_info "Coverage report generated"
}

# 主函数
main() {
    if [ $# -eq 0 ]; then
        show_help
        exit 0
    fi

    COMMAND=$1
    shift

    while [[ $# -gt 0 ]]; do
        case $1 in
            -t|--test)
                TEST_NAME="$2"
                shift 2
                ;;
            -s|--seed)
                SEED="$2"
                shift 2
                ;;
            -w|--wave)
                WAVE=1
                shift
                ;;
            -c|--coverage)
                COVERAGE=1
                shift
                ;;
            -r|--regression)
                REGRESSION="$2"
                shift 2
                ;;
            -h|--help)
                show_help
                exit 0
                ;;
            *)
                print_error "Unknown option: $1"
                show_help
                exit 1
                ;;
        esac
    done

    case $COMMAND in
        compile)
            do_compile
            ;;
        run)
            do_run
            ;;
        regression)
            do_regression
            ;;
        coverage)
            do_coverage
            ;;
        *)
            print_error "Unknown command: $COMMAND"
            show_help
            exit 1
            ;;
    esac
}

main "$@"
