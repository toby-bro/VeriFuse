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
