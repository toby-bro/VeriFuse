#!/bin/bash

FILE=`basename $(find . -maxdepth 1 -name '*.sv' -not -name '*-Yosys.sv' -not -name '*-SV2V.sv' -not -name 'testbench.*' | grep -oP '(?<=\./).*?(?=\.sv)' | sort | head -1)`

echo "Selected FILE: ${FILE}"

wrong_outputs=$(find . -maxdepth 1 -name 'mismatch_*' -exec grep -A100 'Mismatched outputs:' {} \; | grep -oP '^\s{2}\w+(?=:$)' | sort | uniq)

echo "MISMATCHED OUTPUTS:"
echo "${wrong_outputs}"

test_dir=`find . -type d -name 'test_*' | sort -h | head -1`
echo "Selected TEST DIR: ${test_dir}"

cd $test_dir

mkdir -p iverilog verilator cxxrtl cxxslg

cd verilator
cp ../input_* .
echo "===Running Verilator simulation...==="
verilator --binary --exe --build -Mdir obj_dir -sv --timing --assert -Wno-CMPCONST -Wno-DECLFILENAME -Wno-MULTIDRIVEN -Wno-NOLATCH -Wno-UNDRIVEN -Wno-UNOPTFLAT -Wno-UNUSED -Wno-UNSIGNED -Wno-WIDTHEXPAND -Wno-WIDTHTRUNC -Wno-MULTITOP -Wno-ALWCOMBORDER ../../testbench.sv -O3 -I ../../${FILE}.sv && ./obj_dir/Vtestbench

cd ../iverilog
cp ../input_* .
echo "===Running Iverilog simulation...==="
iverilog -o module_sim_iv -g2012 -gsupported-assertions ../../testbench.sv ../../${FILE}.sv && ./module_sim_iv

cd ../cxxrtl
cp ../input_* .
echo "===Running Yosys CXXRTL simulation...==="
yosys -q -p "read_verilog -sv ../../${FILE}.sv; prep -top ${FILE}; write_cxxrtl -O3 ${FILE}.cc"
g++ -std=c++17 -O0 -I$(yosys-config --datdir)/include/backends/cxxrtl/runtime -I. -o testbench ../../testbench.cpp && ./testbench

cd ../cxxslg
cp ../input_* .
echo "===Running Yosys CXXSLG simulation...==="
yosys -q -m slang -p "read_slang ../../${FILE}.sv --top ${FILE}; prep -top ${FILE} ; write_cxxrtl ${FILE}.cc"
g++ -std=c++17 -O0 -I$(yosys-config --datdir)/include/backends/cxxrtl/runtime -I. -o testbench ../../testbench.cpp && ./testbench

echo "===Synth and ran all simulators.==="

cd ..

for output in $wrong_outputs; do
    echo "MISMATCHED OUTPUT SIGNAL: ${output}"
    echo "Verilator output:"
    cat verilator/output_${output}.hex
    echo "Iverilog output:"
    cat iverilog/output_${output}.hex
    echo "CXXRTL output:"
    cat cxxrtl/output_${output}.hex
    echo "CXXSLG output:"
    cat cxxslg/output_${output}.hex
done

cd ..
