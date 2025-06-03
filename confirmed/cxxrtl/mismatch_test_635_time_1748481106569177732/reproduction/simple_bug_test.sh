#!/bin/bash

# Simple 3-way comparison: Verilator vs CXXRTL vs Icarus Verilog
# Tests the negedge register synthesis bug

echo "=== Creating test files ==="

# Create the minimal bug module
cat > bug.sv << 'EOF'
module bug;
    reg [6:0] reg_bug;
    reg clk = 1;
    
    always_ff @(negedge clk)
        reg_bug <= 7'b0011111;
    
    initial begin
        #1 clk = 0;  // negedge trigger
        #1 $display("reg_bug=%b expected=0011111 %s", 
                   reg_bug, reg_bug == 7'b0011111 ? "PASS" : "FAIL");
    end
endmodule
EOF

# Create CXXRTL testbench
cat > cxxrtl_test.cpp << 'EOF'
#include "bug.cc"
#include <iostream>
#include <bitset>

int main() {
    cxxrtl_design::p_bug top;
    for (int i = 0; i < 10; i++) top.step();
    
    return 0;
}
EOF

echo ""
echo "=== Testing with 3 simulators ==="

# Test 1: Icarus Verilog
echo "1. Icarus Verilog:"
iverilog -o sim_iv -g2012 -gsupported-assertions bug.sv 2>/dev/null
if [ -f sim_iv ]; then
    ./sim_iv | grep "reg_bug="
    rm -f sim_iv
else
    echo "   Icarus failed to compile"
fi

# Test 2: Verilator  
echo "2. Verilator:"
verilator --binary --exe --build -sv bug.sv --quiet -o sim_v &>/dev/null
if [ -f obj_dir/sim_v ]; then
    ./obj_dir/sim_v | grep "reg_bug="
    rm -rf obj_dir/
else
    echo "   Verilator failed to compile"
fi

# Test 3: CXXRTL
echo "3. CXXRTL:"
yosys -q -p "read_verilog -sv bug.sv; prep -top bug; write_cxxrtl bug.cc" 2>/dev/null
if [ -f bug.cc ]; then
    g++ -std=c++11 -I$(yosys-config --datdir)/include/backends/cxxrtl/runtime cxxrtl_test.cpp -o sim_c 2>/dev/null
    if [ -f sim_c ]; then
        ./sim_c
        rm -f sim_c bug.cc
    else
        echo "   CXXRTL compile failed"
    fi
else
    echo "   CXXRTL generation failed"
fi

# Cleanup
rm bug.sv cxxrtl_test.cpp
