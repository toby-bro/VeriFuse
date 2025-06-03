#!/bin/bash

rm -rf minimal_test
mkdir -p minimal_test/verilator
mkdir -p minimal_test/cxxrtl

# Copy inputs
cp input_in_data.hex minimal_test/verilator/
cp input_in_data.hex minimal_test/cxxrtl/
cp cxxrtl_testbench_minimal.cpp minimal_test/cxxrtl/testbench.cpp

# Test Verilator
cd minimal_test/verilator
cp ../../top_minimal.sv .
verilator --binary --exe --build -Mdir obj_dir -sv --assert -Wno-CMPCONST -Wno-DECLFILENAME -Wno-MULTIDRIVEN -Wno-NOLATCH -Wno-UNDRIVEN -Wno-UNOPTFLAT -Wno-UNUSED -Wno-UNSIGNED -Wno-WIDTHEXPAND -Wno-WIDTHTRUNC -Wno-MULTITOP -Wno-ALWCOMBORDER ../../testbench_minimal.sv -O3 --quiet &> compile.log && ./obj_dir/Vtestbench_minimal > exec.log && echo "Verilator: Execution successful"

# Test CXXRTL
cd ../cxxrtl
yosys -q -p "read_verilog -sv ../../top_minimal.sv ; prep -top topi ; write_cxxrtl topi.cc" && g++ --std=c++11 -I ~/Documents/Berkeley/yosys/backends/cxxrtl/runtime testbench.cpp -o simulator &> compile.log && ./simulator > exec.log && echo "CXXRTL execution successful"

cd ../..
echo "MINIMAL TEST RESULTS"
echo "verilator $(cat minimal_test/verilator/output_inj_param_out_547.hex)"
echo "cxxrtl $(cat minimal_test/cxxrtl/output_inj_param_out_547.hex)"
