#!/bin/bash

# Script to compare Verilator vs Yosys CXXRTL output for the negedge register bug
# This demonstrates that Verilator works correctly but CXXRTL fails due to Yosys synthesis bug

set -e

echo "========================================"
echo "Comparing Verilator vs Yosys CXXRTL"
echo "Testing negedge register synthesis bug"
echo "========================================"

# Clean up any previous files
rm -f verilator_tb verilator_tb.cpp cxxrtl_tb cxxrtl_tb.cpp bug_test.cpp
rm -rf obj_dir/

echo
echo "1. Testing with Verilator..."
echo "----------------------------"

# Create Verilator testbench
cat > verilator_tb.cpp << 'EOF'
#include <iostream>
#include <verilated.h>
#include "Vbug.h"

int main() {
    Vbug* dut = new Vbug;
    
    // Initialize
    dut->eval();
    
    std::cout << "Verilator simulation complete." << std::endl;
    std::cout << "Note: Internal register access requires --public or specific flags" << std::endl;
    std::cout << "The key test is whether synthesis preserves the negedge behavior" << std::endl;
    
    delete dut;
    return 0; // Assume success for now
}
EOF

# Create a simple Verilog wrapper that exposes the register for testing
cat > bug_wrapper.sv << 'EOF'
module bug_wrapper (
    output logic [6:0] reg_out,
    output logic clk_out
);
    bug dut();
    assign reg_out = dut.reg_bug;
    assign clk_out = dut.clk;
endmodule
EOF

# Create updated testbench for wrapper
cat > verilator_tb_wrapper.cpp << 'EOF'
#include <iostream>
#include <verilated.h>
#include "Vbug_wrapper.h"

int main() {
    Vbug_wrapper* dut = new Vbug_wrapper;
    
    // Initialize
    dut->eval();
    
    std::cout << "=== Verilator Test Results ===" << std::endl;
    std::cout << "Initial state:" << std::endl;
    std::cout << "  clk: " << (int)dut->clk_out << std::endl;
    std::cout << "  reg_bug: 0b";
    for (int i = 6; i >= 0; i--) {
        std::cout << ((dut->reg_out >> i) & 1);
    }
    std::cout << " (decimal: " << (int)dut->reg_out << ")" << std::endl;
    
    // Simulate time progression - the initial block should trigger
    for (int cycle = 0; cycle < 10; cycle++) {
        dut->eval();
        std::cout << "Cycle " << cycle << ":" << std::endl;
        std::cout << "  clk: " << (int)dut->clk_out << std::endl;
        std::cout << "  reg_bug: 0b";
        for (int i = 6; i >= 0; i--) {
            std::cout << ((dut->reg_out >> i) & 1);
        }
        std::cout << " (decimal: " << (int)dut->reg_out << ")" << std::endl;
    }
    
    // Check assertion
    bool assertion_passes = (dut->reg_out == 0b0011111);
    std::cout << "Final assertion (reg_bug == 7'b0011111): " << (assertion_passes ? "PASS" : "FAIL") << std::endl;
    std::cout << "Expected: 0b0011111 (31), Got: 0b";
    for (int i = 6; i >= 0; i--) {
        std::cout << ((dut->reg_out >> i) & 1);
    }
    std::cout << " (" << (int)dut->reg_out << ")" << std::endl;
    
    delete dut;
    return assertion_passes ? 0 : 1;
}
EOF

# Compile with Verilator
echo "Compiling with Verilator..."
verilator --timing -Wall --cc --exe --build bug_wrapper.sv verilator_tb_wrapper.cpp -o verilator_tb

# Run Verilator simulation
echo "Running Verilator simulation:"
VERILATOR_RESULT=0
./obj_dir/verilator_tb || VERILATOR_RESULT=$?

echo
echo "2. Testing with Yosys CXXRTL..."
echo "-------------------------------"

# Generate CXXRTL code
echo "Generating CXXRTL code..."
yosys -p "read_verilog -sv bug.sv; proc; write_cxxrtl cxxrtl_tb.cpp" > /dev/null 2>&1

# Create CXXRTL testbench
cat > cxxrtl_test.cpp << 'EOF'
#include <iostream>
#include <backends/cxxrtl/runtime/cxxrtl/cxxrtl.h>

#include "cxxrtl_tb.cpp"

int main() {
    cxxrtl_design::p_bug top;
    
    // Initialize
    top.step();
    
    std::cout << "=== CXXRTL Test Results ===" << std::endl;
    auto reg_bug_val = top.p_reg__bug.get<uint32_t>();
    std::cout << "Initial state:" << std::endl;
    std::cout << "  reg_bug: 0b";
    for (int i = 6; i >= 0; i--) {
        std::cout << ((reg_bug_val >> i) & 1);
    }
    std::cout << " (decimal: " << reg_bug_val << ")" << std::endl;
    
    // Simulate time progression
    for (int cycle = 0; cycle < 10; cycle++) {
        top.step();
        reg_bug_val = top.p_reg__bug.get<uint32_t>();
        std::cout << "Cycle " << cycle << ":" << std::endl;
        std::cout << "  reg_bug: 0b";
        for (int i = 6; i >= 0; i--) {
            std::cout << ((reg_bug_val >> i) & 1);
        }
        std::cout << " (decimal: " << reg_bug_val << ")" << std::endl;
    }
    
    // Check assertion
    bool assertion_passes = (reg_bug_val == 0b0011111);
    std::cout << "Final assertion (reg_bug == 7'b0011111): " << (assertion_passes ? "PASS" : "FAIL") << std::endl;
    std::cout << "Expected: 0b0011111 (31), Got: 0b";
    for (int i = 6; i >= 0; i--) {
        std::cout << ((reg_bug_val >> i) & 1);
    }
    std::cout << " (" << reg_bug_val << ")" << std::endl;
    
    return assertion_passes ? 0 : 1;
}
EOF

# Compile CXXRTL testbench
echo "Compiling CXXRTL testbench..."
g++ -std=c++14 -I$(yosys-config --datdir)/include -O2 cxxrtl_test.cpp -o cxxrtl_tb

# Run CXXRTL simulation
echo "Running CXXRTL simulation:"
CXXRTL_RESULT=0
./cxxrtl_tb || CXXRTL_RESULT=$?

echo
echo "========================================"
echo "COMPARISON RESULTS:"
echo "========================================"
echo "Verilator result: $([ $VERILATOR_RESULT -eq 0 ] && echo "PASS (assertion holds)" || echo "FAIL (assertion fails)")"
echo "CXXRTL result:    $([ $CXXRTL_RESULT -eq 0 ] && echo "PASS (assertion holds)" || echo "FAIL (assertion fails)")"
echo

if [ $VERILATOR_RESULT -eq 0 ] && [ $CXXRTL_RESULT -ne 0 ]; then
    echo "✓ BUG CONFIRMED: Verilator works correctly, CXXRTL fails"
    echo "  This demonstrates the Yosys synthesis bug where negedge registers"
    echo "  with conflicting clock drivers get connected to constant clocks."
    exit 0
elif [ $VERILATOR_RESULT -ne 0 ] && [ $CXXRTL_RESULT -eq 0 ]; then
    echo "✗ UNEXPECTED: CXXRTL works but Verilator fails"
    exit 1
elif [ $VERILATOR_RESULT -eq 0 ] && [ $CXXRTL_RESULT -eq 0 ]; then
    echo "? BOTH PASS: Either bug is fixed or test is invalid"
    exit 2
else
    echo "? BOTH FAIL: Both simulators fail - unexpected result"
    exit 3
fi
