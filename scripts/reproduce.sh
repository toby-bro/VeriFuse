#!/bin/bash

# Parse command line arguments
VERBOSE=false
while [[ $# -gt 0 ]]; do
    case $1 in
        -v|--verbose)
            VERBOSE=true
            shift
            ;;
        *)
            echo "Unknown option: $1"
            echo "Usage: $0 [-v|--verbose]"
            exit 1
            ;;
    esac
done

# Set output redirect based on verbose flag
if [ "$VERBOSE" = true ]; then
    OUTPUT="/dev/stdout"
else
    OUTPUT="/dev/null"
    echo "Running in quiet mode. Use -v or --verbose to see detailed output."
fi

FILE=`basename $(find . -maxdepth 1 -name '*.sv' -not -name '*-Yosys.sv' -not -name '*-SV2V.sv' -not -name 'testbench.*' | grep -oP '(?<=\./).*?(?=\.sv)' | sort | head -1)`
testbench_generator="$(git rev-parse --show-toplevel)/testbench"

echo "Selected FILE: ${FILE}"

wrong_outputs=$(find . -maxdepth 1 -name 'mismatch_*' -exec grep -A100 'Mismatched outputs:' {} \; | grep -oP '^\s{2}\w+(?=:$)' | sort | uniq)

echo "MISMATCHED OUTPUTS:"
echo "${wrong_outputs}"

test_dir=`find . -type d -name 'test_*' | sort -h | head -1`
echo "Selected TEST DIR: ${test_dir}"

cd $test_dir

mkdir -p iverilog verilator cxxrtl cxxslg
$testbench_generator -d . -n -top ${FILE} ../${FILE}.sv

cd verilator
cp ../input_* .
echo "===Running Verilator simulation...==="
verilator --binary --exe --build -Mdir obj_dir -sv --timing --assert -Wno-CMPCONST -Wno-DECLFILENAME -Wno-MULTIDRIVEN -Wno-NOLATCH -Wno-UNDRIVEN -Wno-UNOPTFLAT -Wno-UNUSED -Wno-UNSIGNED -Wno-WIDTHEXPAND -Wno-WIDTHTRUNC -Wno-MULTITOP -Wno-ALWCOMBORDER ../testbench.sv -O3 -I ../../${FILE}.sv > "$OUTPUT" 2>&1 && ./obj_dir/Vtestbench > "$OUTPUT" 2>&1
vtor_success=$?
if [ $vtor_success -ne 0 ]; then
    echo "Verilator simulation failed. Check output for details."
fi

cd ../iverilog
cp ../input_* .
echo "===Running Iverilog simulation...==="
iverilog -o module_sim_iv -g2012 -gsupported-assertions ../testbench.sv ../../${FILE}.sv > "$OUTPUT" 2>&1 && ./module_sim_iv > "$OUTPUT" 2>&1
iv_success=$?
if [ $iv_success -ne 0 ]; then
    echo "Iverilog simulation failed. Check output for details."
fi

cd ../cxxrtl
cp ../input_* .
echo "===Running Yosys CXXRTL simulation...==="
yosys -q -p "read_verilog -sv ../../${FILE}.sv; prep -top ${FILE}; write_cxxrtl -O3 ${FILE}.cc" > "$OUTPUT" 2>&1
g++ -std=c++17 -O0 -I$(yosys-config --datdir)/include/backends/cxxrtl/runtime -I. -o testbench ../testbench.cpp > "$OUTPUT" 2>&1 && ./testbench > "$OUTPUT" 2>&1
cxxrtl_success=$?
if [ $cxxrtl_success -ne 0 ]; then
    echo "CXXRTL simulation failed. Check output for details."
fi

cd ../cxxslg
cp ../input_* .
echo "===Running Yosys CXXSLG simulation...==="
yosys -q -m slang -p "read_slang ../../${FILE}.sv --top ${FILE}; prep -top ${FILE} ; write_cxxrtl ${FILE}.cc" > "$OUTPUT" 2>&1
g++ -std=c++17 -O0 -I$(yosys-config --datdir)/include/backends/cxxrtl/runtime -I. -o testbench ../testbench.cpp > "$OUTPUT" 2>&1 && ./testbench > "$OUTPUT" 2>&1
cxxslg_success=$?
if [ $cxxslg_success -ne 0 ]; then
    echo "CXXSLG simulation failed. Check output for details."
fi

echo "===Synth and ran all simulators.==="

cd ..

for output in $wrong_outputs; do
    echo "MISMATCHED OUTPUT SIGNAL: ${output}"
    if [ $vtor_success -eq 0 ]; then
    echo "Verilator output:"
    cat verilator/output_${output}.hex
    fi
    if [ $iv_success -eq 0 ]; then
    echo "Iverilog output:"
    cat iverilog/output_${output}.hex
    fi
    if [ $cxxrtl_success -eq 0 ]; then
    echo "CXXRTL output:"
    cat cxxrtl/output_${output}.hex
    fi
    if [ $cxxslg_success -eq 0 ]; then
    echo "CXXSLG output:"
    cat cxxslg/output_${output}.hex
    fi
done

cd ..
