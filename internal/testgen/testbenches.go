package testgen

// svTestbenchTemplate is the template for SystemVerilog testbenches
// Parameters:
// 1. Declarations
// 2. Module instance
// 3. Input count
// 4. Input read code
// 5. Reset toggle code
// 6. Output count
// 7. Output write code
const svTestbenchTemplate = `// filepath: testbench.sv
module testbench;
%s
%s

    initial begin
        string line;
        int fd;
        int status;
        
        // Read %d input files
%s
        
        // Toggle reset if a reset signal was identified
%s
        
        // Allow module to process
        #1;
        
        // Write %d output files
%s
        
        $finish;
    end
endmodule`

// cppTestbenchTemplate is the template for C++ testbenches
// Parameters:
// 1. Module name
// 2. Module name
// 3. Module name (repeated)
// 4. Input declarations
// 5. Input reads
// 6. Input application
// 7. Clock handling code
// 8. Output writes
const cppTestbenchTemplate = `// filepath: testbench.cpp
#include <verilated.h>
#include "V%s_mocked.h"
#include <fstream>
#include <iostream>
#include <iomanip>
#include <cstdint>
#include <string>

int main(int argc, char** argv) {
    // Create context and module
    VerilatedContext* contextp = new VerilatedContext;
    contextp->commandArgs(argc, argv);
    
    V%s_mocked* dut = new V%s_mocked{contextp};

    // Declare input variables
%s
    
    // Read input values
%s
    
    // Apply inputs
%s
    
    // Handle clock toggling and evaluation
%s
    
    // Write outputs
%s
    
    // Clean up
    delete dut;
    delete contextp;
    return 0;
}
`
