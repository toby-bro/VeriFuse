#!/bin/bash

rm -rf ultra_minimal_test
mkdir -p ultra_minimal_test/verilator
mkdir -p ultra_minimal_test/cxxrtl

# Copy inputs
cp input_in_data.hex ultra_minimal_test/verilator/
cp input_clkin_data.hex ultra_minimal_test/verilator/
cp input_in_data.hex ultra_minimal_test/cxxrtl/
cp input_clkin_data.hex ultra_minimal_test/cxxrtl/
cp cxxrtl_testbench_ultra_minimal.cpp ultra_minimal_test/cxxrtl/testbench.cpp

# Test Verilator
cd ultra_minimal_test/verilator
cp ../../top_ultra_minimal.sv .
verilator --binary --exe --build -Mdir obj_dir -sv --timing --assert -Wno-CMPCONST -Wno-DECLFILENAME -Wno-MULTIDRIVEN -Wno-NOLATCH -Wno-UNDRIVEN -Wno-UNOPTFLAT -Wno-UNUSED -Wno-UNSIGNED -Wno-WIDTHEXPAND -Wno-WIDTHTRUNC -Wno-MULTITOP -Wno-ALWCOMBORDER ../../testbench_ultra_minimal.sv -O3 --quiet &> compile.log && ./obj_dir/Vtestbench_ultra_minimal > exec.log && echo "Verilator: Execution successful"

# Test CXXRTL
cd ../cxxrtl
yosys -q -p "read_verilog -sv ../../top_ultra_minimal.sv ; prep -top topi ; write_cxxrtl topi.cc" && g++ --std=c++11 -I ~/Documents/Berkeley/yosys/backends/cxxrtl/runtime testbench.cpp -o simulator &> compile.log && ./simulator > exec.log && echo "CXXRTL execution successful"

cd ../..
echo "ULTRA MINIMAL TEST RESULTS"
echo "verilator $(cat ultra_minimal_test/verilator/output_inj_param_out_547.hex)"
echo "cxxrtl $(cat ultra_minimal_test/cxxrtl/output_inj_param_out_547.hex)"
