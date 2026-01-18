#!/bin/bash
# YaoGuang SoC FPGA Build Script
# Xilinx Versal ACAP

set -e

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

# 路径定义
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(dirname "$SCRIPT_DIR")/../.."
RTL_DIR="$ROOT_DIR/04_Design_RTL"
CV_DIR="$ROOT_DIR/06_Verification_CV"
FPGA_DIR="$CV_DIR/fpga"

# 默认配置
PART="xcv1902"
PACKAGE="ffvd1156"
SPEED="-2"
TOP_MODULE="yaoguang_soc_top"

print_info() {
    echo -e "${GREEN}[INFO]${NC} $1"
}

print_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

show_help() {
    echo "YaoGuang SoC FPGA Build Script"
    echo ""
    echo "Usage: $0 <command> [options]"
    echo ""
    echo "Commands:"
    echo "  synth      Run synthesis only"
    echo "  impl       Run implementation"
    echo "  bitstream  Generate bitstream"
    echo "  all        Full build (synth + impl + bitstream)"
    echo "  program    Program FPGA"
    echo "  clean      Clean build files"
    echo ""
    echo "Options:"
    echo "  -p, --part <part>     FPGA part (default: xcv1902)"
    echo "  -t, --top <module>    Top module (default: yaoguang_soc_top)"
    echo "  -v, --verbose         Verbose output"
    echo "  -h, --help            Show this help"
}

# 检查依赖
check_dependencies() {
    print_info "Checking dependencies..."
    
    # 检查 Vivado
    if ! command -v vivado &> /dev/null; then
        print_error "Vivado not found. Please source Vivado settings."
        exit 1
    fi
    
    print_info "Vivado found: $(which vivado)"
}

# 清理函数
clean_build() {
    print_info "Cleaning build files..."
    
    rm -rf build/
    rm -f *.jou
    rm -f *.log
    
    print_info "Clean completed"
}

# 综合
run_synthesis() {
    print_info "Running synthesis..."
    
    mkdir -p build/synth
    
    vivado -mode batch -source scripts/synth.tcl \
        -tclargs \
        -part $PART \
        -package $PACKAGE \
        -speed $SPEED \
        -top $TOP_MODULE \
        -rtl_dir $RTL_DIR \
        -output_dir build/synth
    
    if [ -f "build/synth/${TOP_MODULE}.dcp" ]; then
        print_info "Synthesis completed successfully"
    else
        print_error "Synthesis failed"
        exit 1
    fi
}

# 实现
run_implementation() {
    print_info "Running implementation..."
    
    if [ ! -f "build/synth/${TOP_MODULE}.dcp" ]; then
        print_warn "Synthesis not found, running synthesis first..."
        run_synthesis
    fi
    
    mkdir -p build/impl
    
    vivado -mode batch -source scripts/impl.tcl \
        -tclargs \
        -input_checkpoint build/synth/${TOP_MODULE}.dcp \
        -output_dir build/impl
    
    if [ -f "build/impl/${TOP_MODULE}.dcp" ]; then
        print_info "Implementation completed successfully"
    else
        print_error "Implementation failed"
        exit 1
    fi
}

# 生成比特流
generate_bitstream() {
    print_info "Generating bitstream..."
    
    if [ ! -f "build/impl/${TOP_MODULE}.dcp" ]; then
        print_warn "Implementation not found, running implementation first..."
        run_implementation
    fi
    
    mkdir -p build/bitstream
    
    vivado -mode batch -source scripts/bitstream.tcl \
        -tclargs \
        -input_checkpoint build/impl/${TOP_MODULE}.dcp \
        -output_dir build/bitstream
    
    if [ -f "build/bitstream/${TOP_MODULE}.bit" ]; then
        print_info "Bitstream generated: build/bitstream/${TOP_MODULE}.bit"
    else
        print_error "Bitstream generation failed"
        exit 1
    fi
}

# 完整构建
run_all() {
    print_info "Running full FPGA build..."
    
    check_dependencies
    run_synthesis
    run_implementation
    generate_bitstream
    
    print_info "FPGA build completed!"
}

# 烧录FPGA
program_fpga() {
    print_info "Programming FPGA..."
    
    if [ ! -f "build/bitstream/${TOP_MODULE}.bit" ]; then
        print_error "Bitstream not found. Please run 'all' first."
        exit 1
    fi
    
    # 检测FPGA板卡
    print_info "Detecting FPGA board..."
    
    vivado -mode batch -source scripts/program.tcl \
        -tclargs \
        -bitstream build/bitstream/${TOP_MODULE}.bit
    
    print_info "FPGA programming completed"
}

# 解析命令行参数
while [[ $# -gt 0 ]]; do
    case $1 in
        synth|impl|bitstream|all|program|clean)
            COMMAND=$1
            shift
            ;;
        -p|--part)
            PART="$2"
            shift 2
            ;;
        -t|--top)
            TOP_MODULE="$2"
            shift 2
            ;;
        -v|--verbose)
            VERBOSE=1
            shift
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

# 执行命令
case $COMMAND in
    synth)
        run_synthesis
        ;;
    impl)
        run_implementation
        ;;
    bitstream)
        generate_bitstream
        ;;
    all)
        run_all
        ;;
    program)
        program_fpga
        ;;
    clean)
        clean_build
        ;;
    *)
        show_help
        exit 1
        ;;
esac
