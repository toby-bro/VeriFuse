#!/bin/bash

rm -r cxxrtl
rm -r verilator


mkdir -p ./verilator
mkdir -p ./cxxrtl
cp input_* ./verilator
cp input_* ./cxxrtl
cp cxxrtl_sim_testbench.cpp cxxrtl/testbench.cpp

# Verilator
cd verilator 
verilator --binary --exe --build -Mdir obj_dir -sv --timing --assert -Wno-CMPCONST -Wno-DECLFILENAME -Wno-MULTIDRIVEN -Wno-NOLATCH -Wno-UNDRIVEN -Wno-UNOPTFLAT -Wno-UNUSED -Wno-UNSIGNED -Wno-WIDTHEXPAND -Wno-WIDTHTRUNC -Wno-MULTITOP -Wno-ALWCOMBORDER ../testbench.sv -O3 --quiet &> compile.log && ./obj_dir/Vtestbench > exec.log && echo "Verilator: Execution successful"

# CXXRTL

cd ../cxxrtl
yosys -q -p "read_verilog -sv ../top_100.sv ; prep -top topi ; write_cxxrtl topi.cc" && g++ --std=c++11 -I ~/Documents/Berkeley/yosys/backends/cxxrtl/runtime testbench.cpp -o simulator &> compile.log && ./simulator > exec.log && echo "CXXRTL execution successful"
cd ..
echo "FINAL OUTPUTS"
echo "verilator $(cat verilator/output_inj_param_out_547.hex)"
echo "cxxrtl $(cat cxxrtl/output_inj_param_out_547.hex)"
