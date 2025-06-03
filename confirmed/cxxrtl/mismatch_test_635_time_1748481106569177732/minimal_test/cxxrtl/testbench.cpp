// Minimal CXXRTL testbench
#include "topi.cc"
#include <fstream>
#include <iostream>
#include <iomanip>
#include <cstdint>
#include <string>

int main(int argc, char** argv) {
    cxxrtl_design::p_topi topi_i;

    // Read input
    std::ifstream in_data_file("input_in_data.hex");
    if (!in_data_file.is_open()) {
        std::cerr << "Failed to open input_in_data.hex" << std::endl;
        return 1;
    }
    std::string in_data_hex_str;
    in_data_file >> in_data_hex_str;
    in_data_file.close();

    // Parse hex string to CXXRTL value
    cxxrtl::value<192> in_data;
    size_t total_hex_chars = 192 / 4;
    if (in_data_hex_str.length() < total_hex_chars) {
        in_data_hex_str.insert(0, total_hex_chars - in_data_hex_str.length(), '0');
    } else if (in_data_hex_str.length() > total_hex_chars) {
        in_data_hex_str = in_data_hex_str.substr(in_data_hex_str.length() - total_hex_chars);
    }

    const size_t num_chunks = cxxrtl::value<192>::chunks;
    const size_t hex_chars_per_chunk = cxxrtl::value<192>::chunk::bits / 4;

    for (size_t i = 0; i < num_chunks; ++i) {
        size_t data_idx = i;
        size_t str_offset = (num_chunks - 1 - i) * hex_chars_per_chunk;
        std::string chunk_hex_str = in_data_hex_str.substr(str_offset, hex_chars_per_chunk);
        in_data.data[data_idx] = std::stoull(chunk_hex_str, nullptr, 16);
    }

    // Apply input
    topi_i.p_in__data = in_data;
    
    // Evaluate combinational logic
    topi_i.step();
    topi_i.step();

    // Write output
    std::ofstream output_file("output_inj_param_out_547.hex");
    if (!output_file.is_open()) {
        std::cerr << "Failed to open output file" << std::endl;
        return 1;
    }
    
    uint8_t value = topi_i.p_inj__param__out__547.get<uint8_t>();
    for (int i = 7; i >= 0; i--) {
        output_file << ((value >> i) & 1);
    }
    output_file << std::endl;
    output_file.close();

    return 0;
}
