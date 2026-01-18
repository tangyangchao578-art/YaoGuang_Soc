#!/bin/bash
# YaoGuang SoC DV Simulation Runner

set -e

DV_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ROOT_DIR="$(dirname "$DV_DIR")"

SIMULATOR=${SIMULATOR:-vcs}
TEST_NAME=${TEST_NAME:-"test_basic"}
SEED=${SEED:-"random"}
WAVE=${WAVE:-0}
COVERAGE=${COVERAGE:-1}

compile() {
    echo "[INFO] Compiling verification environment..."
    vcs -full64 -sverilog -f "$DV_DIR/uvm_env/filelist/uvm.f" -top top_tb +vcs+lic_wait
    echo "[INFO] Compilation completed"
}

run_test() {
    echo "[INFO] Running test: $TEST_NAME"
    simv +UVM_TESTNAME="$TEST_NAME" +ntb_random_seed="$SEED"
    echo "[INFO] Test passed: $TEST_NAME"
}

case "$1" in
    compile)
        compile
        ;;
    run)
        run_test
        ;;
    *)
        echo "Usage: $0 {compile|run} [-t test_name] [-s seed] [-w] [-c]"
        exit 1
        ;;
esac
