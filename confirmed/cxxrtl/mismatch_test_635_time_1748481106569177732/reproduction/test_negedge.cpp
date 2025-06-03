#include "negedge_debug.cc"
#include <iostream>
#include <bitset>

int main() {
    cxxrtl_design::p_top top;
    
    std::cout << "Initial reg_bug: " << std::bitset<7>(top.p_reg__bug.get<uint32_t>()) << std::endl;
    
    // Set clock high initially
    top.p_clk = value<1>{1u};
    top.eval();
    top.commit();
    
    std::cout << "After reset, reg_bug: " << std::bitset<7>(top.p_reg__bug.get<uint32_t>()) << std::endl;
    
    // Create negedge: 1 -> 0
    top.p_clk = value<1>{0u};
    top.eval();
    top.commit();
    
    std::cout << "After negedge, reg_bug: " << std::bitset<7>(top.p_reg__bug.get<uint32_t>()) << std::endl;
    std::cout << "Expected:       0011111" << std::endl;
    
    bool pass = top.p_reg__bug.get<uint32_t>() == 0x1f;
    std::cout << "Result: " << (pass ? "PASS" : "FAIL") << std::endl;
    
    return 0;
}
