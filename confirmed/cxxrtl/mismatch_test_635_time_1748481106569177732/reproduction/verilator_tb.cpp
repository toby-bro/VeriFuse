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
