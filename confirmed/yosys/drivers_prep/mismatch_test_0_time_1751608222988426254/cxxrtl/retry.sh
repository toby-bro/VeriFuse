#!/bin/bash
rm output_sum.hex a.out simple_sub.cc
yosys -q -p "read_verilog -sv ../simple_sub.sv; prep -top simple_sub; write_cxxrtl simple_sub.cc"
g++ -std=c++17 -O0 -I$(yosys-config --datdir)/include/backends/cxxrtl/runtime testbench.cpp -I.
./a.out
cat output_sum.hex
