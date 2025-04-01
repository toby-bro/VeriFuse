#include <verilated.h>
#include "Vibex_branch_predict.h"
#include <fstream>
#include <iostream>
#include <cstdint>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    Vibex_branch_predict* dut = new Vibex_branch_predict;

    // Read input values
    std::ifstream input_file("input.hex");
    std::ifstream pc_file("pc.hex");
    std::ifstream valid_file("valid.hex");
    
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
    std::ofstream taken_file("taken.hex");
    std::ofstream target_file("target.hex");
    
    taken_file << (int)dut->predict_branch_taken_o;
    target_file << std::hex << dut->predict_branch_pc_o;

    delete dut;
    return 0;
}
