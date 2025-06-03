#!/bin/bash

# ULTRA-MINIMAL CXXRTL negedge bug reproduction (Test case 635)
# Bug: negedge-triggered register with async reset fails to update in CXXRTL

echo "=== Writing the files ==="
cat > ultra_minimal.sv << 'EOF'
// Ultra-minimal CXXRTL negedge bug - just the core issue
module bug;
    // Hardcoded values from test case 635
    wire reset = 1'b0;  // No reset (bit 32 of clkin_data = 0)
    wire [6:0] expected_data = 7'b0011111;  // Expected register value
    
    reg [6:0] reg_bug;
    reg clk = 1;
    
    // THE BUG: negedge register fails to update in CXXRTL
    always_ff @(negedge clk, posedge reset)
        if (reset)
            reg_bug <= 7'h00;
        else 
            reg_bug <= expected_data;
    
    initial begin
        #1 clk = 0;  // negedge trigger
        #1 $display("reg_bug=%b expected=0011111 %s", 
                   reg_bug, reg_bug == 7'b0011111 ? "✓" : "✗");
    end
endmodule
EOF
cat > ultra_test.cpp << 'EOF'
#include "bug.cc"
#include <iostream>
#include <bitset>

int main() {
    cxxrtl_design::p_bug top;
    for (int i = 0; i < 5; i++) top.step();
    
    uint32_t result = top.p_reg__bug.get<uint32_t>();
    std::cout << "CXXRTL reg_bug=" << std::bitset<7>(result) 
              << " expected=0011111 " << (result == 0b0011111 ? "✓" : "✗") << std::endl;
    return 0;
}
EOF

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
