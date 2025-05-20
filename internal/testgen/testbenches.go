package testgen

// svTestbenchTemplate is the template for SystemVerilog testbenches
// Parameters:
// 1. Include directive for the mocked module
// 2. Declarations
// 3. Module instance
// 4. Input count
// 5. Input read code
// 6. Reset toggle code
// 7. Clock toggle code
// 8. Output count
// 9. Output write code
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

        // Toggle clock signals
%s

        // Allow module to process
        #1;

        // Write %d output files
%s

        $finish;
    end
endmodule`

// cxxrtlTestbenchTemplate is the template for C++ testbenches
// Parameters:
// 1. Module name (for include directive, e.g., "my_module")
// 2. Module name (for CXXRTL class name, e.g., "my_module" -> cxxrtl_design::p_my_module)
// 3. Module instance name (e.g., "my_module_i")
// 4. Input declarations
// 5. Input reads
// 6. Input application
// 7. Clock handling and evaluation code
// 8. Output writes
const cxxrtlTestbenchTemplate = `// filepath: cxxrtl_testbench.cpp
#include "%s.h" // CXXRTL generated header for the module
// You might need a common CXXRTL include, e.g.:
// #include "cxxrtl_lib.h" 

#include <fstream>
#include <iostream>
#include <iomanip>
#include <cstdint>
#include <string>

// Assuming the CXXRTL-generated code uses a 'cxxrtl_design' namespace 
// and prefixes the module class with 'p_'. Adjust if your CXXRTL setup differs.
int main(int argc, char** argv) {
    cxxrtl_design::p_%s %s_i; // DUT instance: cxxrtl_design::p_MODULE_NAME instance_name_i;

    // Declare input variables
%s
    
    // Read input values
%s
    
    // Apply inputs to DUT
%s
    
    // Handle reset, clock toggling, and evaluation
%s
    
    // Write outputs from DUT
%s
    
    // CXXRTL objects on the stack are cleaned up automatically
    return 0;
}
`
