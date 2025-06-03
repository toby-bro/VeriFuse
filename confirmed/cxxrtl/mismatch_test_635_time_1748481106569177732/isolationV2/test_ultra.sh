#!/bin/bash

# ULTRA-MINIMAL negedge bug reproduction
rm -rf verilator_ultra cxxrtl_ultra icarus_ultra

echo "=== Writing the files ==="
cat > ultra_minimal.sv << 'EOF'
module ultra_minimal (
    input wire clk,
    input wire [3:0] data,
    output wire [3:0] out
);
    reg [3:0] reg1;
    reg [3:0] reg2;
    wire trigger;
    
    // Simple trigger from register comparison
    assign trigger = (reg1 == 4'hA);
    
    // First register - normal positive edge
    always_ff @(posedge clk)
        reg1 <= data;
    
    // Second register - NEGEDGE trigger (this is the bug source)
    always_ff @(negedge trigger)
        reg2 <= data;
    
    // Output
    assign out = reg2;
    
endmodule
EOF

cat > tb_ultra.sv << 'EOF'
// Ultra-minimal testbench
`include "../ultra_minimal.sv"

module tb;
    reg clk;
    reg [3:0] data;
    wire [3:0] out;

    ultra_minimal dut (
        .clk(clk),
        .data(data),
        .out(out)
    );

    initial begin
        clk = 0;
        data = 4'h5;  // Start with non-trigger value
        
        #1;
        clk = 1; #1;  // First clock edge
        clk = 0; #1;
        
        data = 4'hA;  // Set trigger value (reg1 == 4'hA)
        clk = 1; #1;  // Second clock edge
        clk = 0; #1;
        
        data = 4'h3;  // Change data (causes negedge of trigger)
        clk = 1; #1;  // Third clock edge  
        clk = 0; #1;
        
        #5; // Let it settle
        
        // Write result
        $display("Result: %b", out);
        
        // Write to file for comparison
        begin
            integer fd, i;
            fd = $fopen("output_ultra.hex", "w");
            for (i = 3; i >= 0; i = i - 1) begin
                $fwrite(fd, "%b", out[i]);
            end
            $fwrite(fd, "\n");
            $fclose(fd);
        end
        
        $finish;
    end
endmodule
EOF

cat > cxxrtl_ultra.cpp << 'EOF'
#include "ultra_minimal.cc"
#include <fstream>
#include <iostream>
#include <cstdint>

int main() {
    cxxrtl_design::p_ultra__minimal dut;

    // Initialize
    dut.p_clk = cxxrtl::value<1>{0u};
    dut.p_data = cxxrtl::value<4>{5u};  // Start with non-trigger value
    dut.step();
    
    // First clock edge
    dut.p_clk = cxxrtl::value<1>{1u};
    dut.step();
    dut.p_clk = cxxrtl::value<1>{0u};
    dut.step();
    
    // Set trigger value
    dut.p_data = cxxrtl::value<4>{0xAu};  // This makes trigger go high
    
    // Second clock edge
    dut.p_clk = cxxrtl::value<1>{1u};
    dut.step();
    dut.p_clk = cxxrtl::value<1>{0u};
    dut.step();
    
    // Change data to cause negedge
    dut.p_data = cxxrtl::value<4>{3u};  // This should cause negedge of trigger
    
    // Third clock edge
    dut.p_clk = cxxrtl::value<1>{1u};
    dut.step();
    dut.p_clk = cxxrtl::value<1>{0u};
    dut.step();
    
    // Let it settle
    dut.step();
    dut.step();
    dut.step();
    
    // Write result
    std::cout << "Result: ";
    uint8_t result = dut.p_out.get<uint8_t>();
    for (int i = 3; i >= 0; i--) {
        std::cout << ((result >> i) & 1);
    }
    std::cout << std::endl;
    
    // Write to file
    std::ofstream file("output_ultra.hex");
    for (int i = 3; i >= 0; i--) {
        file << ((result >> i) & 1);
    }
    file << std::endl;
    file.close();
    
    return 0;
}
EOF

mkdir -p verilator_ultra cxxrtl_ultra icarus_ultra
cp cxxrtl_ultra.cpp cxxrtl_ultra/testbench.cpp
cp tb_ultra.sv icarus_ultra/

echo "=== ULTRA-MINIMAL NEGEDGE BUG TEST ==="

echo "Running Verilator..."
cd verilator_ultra
verilator --binary --exe --build -Mdir obj_dir -sv --quiet \
    ../tb_ultra.sv &> compile.log

if [ $? -eq 0 ]; then
    ./obj_dir/Vtb_ultra > exec.log && echo "Verilator: SUCCESS"
else
    echo "Verilator FAILED"; cat compile.log; exit 1
fi

echo "Running CXXRTL..."
cd ../cxxrtl_ultra
yosys -q -p "read_verilog -sv ../ultra_minimal.sv ; prep -top ultra_minimal ; write_cxxrtl ultra_minimal.cc"

if [ $? -eq 0 ]; then
    g++ --std=c++11 -I ~/Documents/Berkeley/yosys/backends/cxxrtl/runtime testbench.cpp -o simulator &> compile.log
    if [ $? -eq 0 ]; then
        ./simulator > exec.log && echo "CXXRTL: SUCCESS"
    else
        echo "CXXRTL compilation FAILED"; cat compile.log; exit 1
    fi
else
    echo "Yosys FAILED"; exit 1
fi

echo "Running Icarus Verilog..."
cd ../icarus_ultra
iverilog -o module_sim_iv -g2012 -gsupported-assertions tb_ultra.sv &> compile.log

if [ $? -eq 0 ]; then
    ./module_sim_iv > exec.log && echo "Icarus Verilog: SUCCESS"
else
    echo "Icarus Verilog FAILED"; cat compile.log; exit 1
fi

cd ..
echo "=== RESULTS ==="
echo "Verilator:      $(cat verilator_ultra/output_ultra.hex)"
echo "CXXRTL:         $(cat cxxrtl_ultra/output_ultra.hex)"
echo "Icarus Verilog: $(cat icarus_ultra/output_ultra.hex)"

# Compare all three results
echo "=== COMPARISON ==="
verilator_result=$(cat verilator_ultra/output_ultra.hex)
cxxrtl_result=$(cat cxxrtl_ultra/output_ultra.hex)
icarus_result=$(cat icarus_ultra/output_ultra.hex)

if [ "$verilator_result" = "$cxxrtl_result" ] && [ "$verilator_result" = "$icarus_result" ]; then
    echo "ALL MATCH ✓"
elif [ "$verilator_result" = "$icarus_result" ]; then
    echo "Verilator and Icarus match, CXXRTL differs - CXXRTL BUG ✗"
elif [ "$cxxrtl_result" = "$icarus_result" ]; then
    echo "CXXRTL and Icarus match, Verilator differs - VERILATOR BUG ✗"
elif [ "$verilator_result" = "$cxxrtl_result" ]; then
    echo "Verilator and CXXRTL match, Icarus differs - ICARUS BUG ✗"
else
    echo "ALL DIFFER! Need more investigation ✗"
fi
