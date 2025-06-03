// Ultra-minimal CXXRTL testbench with proper clock handling
#include "topi.cc"
#include <fstream>
#include <iostream>
#include <iomanip>
#include <cstdint>
#include <string>

int main(int argc, char** argv) {
    cxxrtl_design::p_topi topi_i;

    // Read inputs
    std::ifstream clkin_data_file("input_clkin_data.hex");
    if (!clkin_data_file.is_open()) {
        std::cerr << "Failed to open input_clkin_data.hex" << std::endl;
        return 1;
    }
    std::string clkin_data_hex_str;
    clkin_data_file >> clkin_data_hex_str;
    clkin_data_file.close();

    std::ifstream in_data_file("input_in_data.hex");
    if (!in_data_file.is_open()) {
        std::cerr << "Failed to open input_in_data.hex" << std::endl;
        return 1;
    }
    std::string in_data_hex_str;
    in_data_file >> in_data_hex_str;
    in_data_file.close();

    // Parse clkin_data
    cxxrtl::value<96> clkin_data;
    size_t total_hex_chars_clkin = 96 / 4;
    if (clkin_data_hex_str.length() < total_hex_chars_clkin) {
        clkin_data_hex_str.insert(0, total_hex_chars_clkin - clkin_data_hex_str.length(), '0');
    }
    const size_t num_chunks_clkin = cxxrtl::value<96>::chunks;
    const size_t hex_chars_per_chunk_clkin = cxxrtl::value<96>::chunk::bits / 4;
    for (size_t i = 0; i < num_chunks_clkin; ++i) {
        size_t data_idx = i;
        size_t str_offset = (num_chunks_clkin - 1 - i) * hex_chars_per_chunk_clkin;
        std::string chunk_hex_str = clkin_data_hex_str.substr(str_offset, hex_chars_per_chunk_clkin);
        clkin_data.data[data_idx] = std::stoull(chunk_hex_str, nullptr, 16);
    }

    // Parse in_data
    cxxrtl::value<192> in_data;
    size_t total_hex_chars_in = 192 / 4;
    if (in_data_hex_str.length() < total_hex_chars_in) {
        in_data_hex_str.insert(0, total_hex_chars_in - in_data_hex_str.length(), '0');
    }
    const size_t num_chunks_in = cxxrtl::value<192>::chunks;
    const size_t hex_chars_per_chunk_in = cxxrtl::value<192>::chunk::bits / 4;
    for (size_t i = 0; i < num_chunks_in; ++i) {
        size_t data_idx = i;
        size_t str_offset = (num_chunks_in - 1 - i) * hex_chars_per_chunk_in;
        std::string chunk_hex_str = in_data_hex_str.substr(str_offset, hex_chars_per_chunk_in);
        in_data.data[data_idx] = std::stoull(chunk_hex_str, nullptr, 16);
    }

    // Apply inputs
    topi_i.p_clkin__data = clkin_data;
    topi_i.p_in__data = in_data;

    // Clock toggling - mimic Verilator testbench behavior
    for (int cycle = 0; cycle < 10; cycle++) {
        topi_i.p_clkin__data = cxxrtl::value<96>{0u};
        topi_i.step();
        topi_i.p_clkin__data = cxxrtl::value<96>{1u};
        topi_i.step();
    }

    // Extra settling steps
    topi_i.step();
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
