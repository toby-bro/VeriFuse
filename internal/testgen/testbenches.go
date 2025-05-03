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
