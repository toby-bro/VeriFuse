package simulator

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"text/template"
)

// VerilatorSimulator represents the Verilator simulator
type VerilatorSimulator struct {
	execPath   string
	workDir    string
	moduleName string
}

// NewVerilatorSimulator creates a new Verilator simulator instance
func NewVerilatorSimulator(workDir string, moduleName string) *VerilatorSimulator {
	return &VerilatorSimulator{
		execPath:   filepath.Join(workDir, "obj_dir", fmt.Sprintf("V%s_mocked", moduleName)),
		workDir:    workDir,
		moduleName: moduleName,
	}
}

// Compile compiles the verilog files with Verilator
func (sim *VerilatorSimulator) Compile() error {
	// Find all SystemVerilog files in work directory - excluding testbench.sv
	moduleFiles := []string{}
	entries, err := os.ReadDir(sim.workDir)
	if err != nil {
		return fmt.Errorf("failed to read work directory: %v", err)
	}

	for _, entry := range entries {
		if !entry.IsDir() && filepath.Ext(entry.Name()) == ".sv" {
			// Skip the SystemVerilog testbench - it's for iverilog only
			if entry.Name() != "testbench.sv" && entry.Name() != "test.sv" {
				moduleFiles = append(moduleFiles, entry.Name())
			}
		}
	}

	if len(moduleFiles) == 0 {
		return fmt.Errorf("no SystemVerilog module files found in %s", sim.workDir)
	}

	// Create Verilator testbench
	testbenchPath := filepath.Join(sim.workDir, "verilator_testbench.cpp")

	// Create a testbench that takes file paths as command-line arguments
	testbench := generateVerilatorTestbench(sim.moduleName)
	if err := os.WriteFile(testbenchPath, []byte(testbench), 0644); err != nil {
		return fmt.Errorf("failed to write Verilator testbench: %v", err)
	}

	// Create the obj_dir in the worker directory
	objDir := filepath.Join(sim.workDir, "obj_dir")
	if err := os.MkdirAll(objDir, 0755); err != nil {
		return fmt.Errorf("failed to create obj_dir: %v", err)
	}

	// Build verilator command with all SV files
	verilatorArgs := []string{
		"--cc", "--exe", "--build", "-Mdir", "obj_dir",
		"--timing", // Add timing option to handle delays
		"verilator_testbench.cpp",
	}
	verilatorArgs = append(verilatorArgs, moduleFiles...)

	// Run Verilator in the worker directory
	cmd := exec.Command("verilator", verilatorArgs...)
	cmd.Dir = sim.workDir

	var stderr bytes.Buffer
	cmd.Stderr = &stderr

	err = cmd.Run()
	if err != nil {
		return fmt.Errorf("verilator compilation failed: %v\n%s", err, stderr.String())
	}

	return nil
}

// RunTest runs the simulator with provided input directory and output paths
func (sim *VerilatorSimulator) RunTest(inputDir string, outputPaths map[string]string) error {
	// Create command line args for all inputs and outputs
	args := []string{}

	// Add the input directory path
	args = append(args, fmt.Sprintf("--input-dir=%s", inputDir))

	// Add output file paths
	for portName, outputPath := range outputPaths {
		args = append(args, fmt.Sprintf("--output-%s=%s", portName, outputPath))
	}

	// Run the simulator with file paths as arguments
	cmd := exec.Command(sim.execPath, args...)
	var stderr bytes.Buffer
	cmd.Stderr = &stderr

	if err := cmd.Run(); err != nil {
		return fmt.Errorf("verilator execution failed: %v - %s", err, stderr.String())
	}

	// Verify output files were created
	for _, outputPath := range outputPaths {
		if _, err := os.Stat(outputPath); os.IsNotExist(err) {
			return fmt.Errorf("output file was not created: %s", outputPath)
		}
	}

	return nil
}

// GetExecPath returns the path to the compiled simulator executable
func (sim *VerilatorSimulator) GetExecPath() string {
	return sim.execPath
}

// generateVerilatorTestbench creates a C++ testbench that accepts file paths as command-line arguments
func generateVerilatorTestbench(moduleName string) string {
	tmpl := template.Must(template.New("verilator_tb").Parse(`
#include <verilated.h>
#include "V{{.ModuleName}}_mocked.h"
#include <fstream>
#include <iostream>
#include <iomanip>  // Added for std::setw, std::setfill
#include <cstdint>
#include <string>
#include <map>
#include <vector>
#include <filesystem>

namespace fs = std::filesystem;

int main(int argc, char** argv) {
    // Parse command line args
    Verilated::commandArgs(argc, argv);
    
    std::string inputDir;
    std::map<std::string, std::string> outputPaths;
    
    // Parse command line arguments
    for (int i = 1; i < argc; i++) {
        std::string arg = argv[i];
        
        // Parse input directory
        if (arg.find("--input-dir=") == 0) {
            inputDir = arg.substr(12);
            continue;
        }
        
        // Parse output file paths
        if (arg.find("--output-") == 0) {
            size_t equalPos = arg.find('=');
            if (equalPos != std::string::npos) {
                std::string portName = arg.substr(9, equalPos-9);
                std::string filePath = arg.substr(equalPos+1);
                outputPaths[portName] = filePath;
            }
        }
    }
    
    if (inputDir.empty()) {
        std::cerr << "Error: No input directory specified (--input-dir)" << std::endl;
        return 1;
    }
    
    // Create the module instance
    V{{.ModuleName}}_mocked* dut = new V{{.ModuleName}}_mocked;
    
    // Find all input files in the input directory
    std::vector<std::string> inputFiles;
    try {
        for (const auto& entry : fs::directory_iterator(inputDir)) {
            if (entry.is_regular_file()) {
                std::string filename = entry.path().filename().string();
                if (filename.find("input_") == 0) {
                    inputFiles.push_back(entry.path().string());
                }
            }
        }
    } catch (const fs::filesystem_error& ex) {
        std::cerr << "Error accessing input directory: " << ex.what() << std::endl;
        delete dut;
        return 1;
    }
    
    if (inputFiles.empty()) {
        std::cerr << "Error: No input files found in " << inputDir << std::endl;
        delete dut;
        return 1;
    }
    
    // Process each input file and apply to DUT
    for (const auto& inputPath : inputFiles) {
        std::string filename = fs::path(inputPath).filename().string();
        // Extract port name from filename (input_portname.hex)
        std::string portName = filename.substr(6);
        portName = portName.substr(0, portName.find("."));
        
        // Open and read the file
        std::ifstream inFile(inputPath);
        if (!inFile.is_open()) {
            std::cerr << "Error opening input file: " << inputPath << std::endl;
            continue;
        }
        
        std::string valueStr;
        inFile >> valueStr;
        inFile.close();
        
        // Apply the value to the appropriate port
        // This approach requires checking for each possible port name
        // It's verbose but avoids using the non-existent setenv method
        
        // Note: Replace this part with actual port assignments for your specific module
        // For example:
        if (portName == "clk_i") {
            dut->clk_i = (valueStr[0] == '1' ? 1 : 0);
        }
        else if (portName == "rst_ni") {
            dut->rst_ni = (valueStr[0] == '1' ? 1 : 0);
        }
        else if (portName == "fetch_valid_i") {
            dut->fetch_valid_i = (valueStr[0] == '1' ? 1 : 0);
        }
        else if (portName == "fetch_rdata_i") {
            dut->fetch_rdata_i = std::stoull(valueStr, nullptr, 16);
        }
        else if (portName == "fetch_pc_i") {
            dut->fetch_pc_i = std::stoull(valueStr, nullptr, 16);
        }
        // Add additional ports as needed
        else {
            std::cerr << "Warning: Unknown port name: " << portName << std::endl;
        }
    }
    
    // Evaluate the model
    dut->eval();
    
    // Write outputs to the specified paths
    for (const auto& output : outputPaths) {
        const std::string& portName = output.first;
        const std::string& filePath = output.second;
        
        std::ofstream outFile(filePath);
        if (!outFile.is_open()) {
            std::cerr << "Error opening output file: " << filePath << std::endl;
            continue;
        }
        
        // Read from the appropriate port and write to file
        // This approach requires checking for each possible port name
        if (portName == "predict_branch_taken_o") {
            outFile << (dut->predict_branch_taken_o ? '1' : '0');
        }
        else if (portName == "predict_branch_pc_o") {
            outFile << std::hex << std::setfill('0') << std::setw(8) << dut->predict_branch_pc_o;
        }
        // Add additional ports as needed
        else {
            std::cerr << "Warning: Unknown output port: " << portName << std::endl;
        }
        
        outFile.close();
    }
    
    // Clean up
    delete dut;
    return 0;
}
`))

	var buf bytes.Buffer
	tmpl.Execute(&buf, struct{ ModuleName string }{ModuleName: moduleName})
	return buf.String()
}
