package testgen

// svTestbenchTemplate is the template for SystemVerilog testbenches
// Parameters:
// 1. Include directive for the mocked module
// 2. Declarations
// 3. Module instance
// 4. Input count
// 5. Input read code
// 6. Reset toggle code
// 7. Output count
// 8. Output write code
const svTestbenchTemplate = `// filepath: testbench.sv
%s // Include the mocked module file

module top;
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
#include "V%s.h"
#include <fstream>
#include <iostream>
#include <iomanip>
#include <cstdint>
#include <string>

int main(int argc, char** argv) {
    // Create context and module
    VerilatedContext* contextp = new VerilatedContext;
    contextp->commandArgs(argc, argv);
    
    V%s* dut = new V%s{contextp};

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
