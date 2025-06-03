#!/bin/bash

# ULTRA-MINIMAL CXXRTL negedge bug reproduction (Test case 635)
# Bug: negedge-triggered register with async reset fails to update in CXXRTL

echo "=== ULTRA-MINIMAL CXXRTL NEGEDGE BUG ==="

echo "1. Verilator test:"
verilator --binary --exe --build -sv ultra_minimal.sv --quiet -o vsim 2>/dev/null
if [ -f obj_dir/vsim ]; then
    ./obj_dir/vsim | grep "reg_bug="
else
    echo "   Verilator failed"
fi

echo ""
echo "2. CXXRTL test:"
yosys -q -p "read_verilog -sv ultra_minimal.sv; prep -top bug; write_cxxrtl bug.cc" 2>/dev/null
if [ -f bug.cc ]; then
    g++ -std=c++11 -I $(yosys-config --datdir)/include/backends/cxxrtl/runtime ultra_test.cpp -o csim 2>/dev/null
    if [ -f csim ]; then
        ./csim
    else
        echo "   CXXRTL compile failed"
    fi
else
    echo "   CXXRTL generation failed"
fi

echo ""
echo "Expected: Verilator ✓, CXXRTL ✗ (confirming negedge bug)"
