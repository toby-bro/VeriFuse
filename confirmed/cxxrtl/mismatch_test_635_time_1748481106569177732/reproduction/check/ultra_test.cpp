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
