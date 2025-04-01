package testgen

// svTestbenchTemplate is the template for SystemVerilog testbenches
const svTestbenchTemplate = `// filepath: testbench.sv
module testbench;
    logic clk_i;
    logic rst_ni;
    logic [31:0] fetch_rdata_i;
    logic [31:0] fetch_pc_i;
    logic        fetch_valid_i;
    logic        predict_branch_taken_o;
    logic [31:0] predict_branch_pc_o;

    ibex_branch_predict_mocked dut (.*);

    initial begin
        string line;
        int fd;
        
        // Read inputs
        fd = $fopen("%s/input.hex", "r");
        $fgets(line, fd);
        $sscanf(line, "%%h", fetch_rdata_i);
        $fclose(fd);
        
        fd = $fopen("%s/pc.hex", "r");
        $fgets(line, fd);
        $sscanf(line, "%%h", fetch_pc_i);
        $fclose(fd);
        
        fd = $fopen("%s/valid.hex", "r");
        $fgets(line, fd);
        $sscanf(line, "%%b", fetch_valid_i);
        $fclose(fd);

        #1;
        
        // Write outputs
        fd = $fopen("%s/taken.hex", "w");
        $fwrite(fd, "%%0b", predict_branch_taken_o);
        $fclose(fd);
        
        fd = $fopen("%s/target.hex", "w");
        $fwrite(fd, "%%h", predict_branch_pc_o);
        $fclose(fd);
        
        $finish;
    end
endmodule`

// cppTestbenchTemplate is the template for C++ testbenches
const cppTestbenchTemplate = `// filepath: testbench.cpp
#include <verilated.h>
#include "Vibex_branch_predict_mocked.h"  // Updated header name
#include <fstream>
#include <iostream>
#include <cstdint>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    Vibex_branch_predict_mocked* dut = new Vibex_branch_predict_mocked;  // Updated class name

    // Read input values
    std::ifstream input_file("%s/input.hex");
    std::ifstream pc_file("%s/pc.hex");
    std::ifstream valid_file("%s/valid.hex");
    
    uint32_t fetch_rdata, fetch_pc;
    uint8_t fetch_valid;
    
    input_file >> std::hex >> fetch_rdata;
    pc_file >> std::hex >> fetch_pc;
    valid_file >> fetch_valid;

    // Apply inputs
    dut->fetch_rdata_i = fetch_rdata;
    dut->fetch_pc_i = fetch_pc;
    dut->fetch_valid_i = fetch_valid;
    dut->clk_i = 0;
    dut->rst_ni = 1;

    // Evaluate
    dut->eval();

    // Write outputs
    std::ofstream taken_file("%s/taken.hex");
    std::ofstream target_file("%s/target.hex");
    
    taken_file << (int)dut->predict_branch_taken_o;
    target_file << std::hex << dut->predict_branch_pc_o;

    delete dut;
    return 0;
}`
