package simulator

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"text/template"

	"github.com/toby-bro/pfuzz/internal/verilog"
)

// VerilatorSimulator represents the Verilator simulator
type VerilatorSimulator struct {
	execPath   string
	workDir    string
	moduleName string
	module     *verilog.Module // Add module reference
}

// NewVerilatorSimulator creates a new Verilator simulator instance
func NewVerilatorSimulator(workDir string, moduleName string) *VerilatorSimulator {
	// Parse the module to get port and parameter information
	moduleFile := filepath.Join(workDir, moduleName+"_mocked.sv")
	module, err := verilog.ParseVerilogFile(moduleFile, moduleName+"_mocked")
	if err != nil {
		// If we can't parse, just continue with nil module - will use generic template
		module = nil
	}

	return &VerilatorSimulator{
		execPath:   filepath.Join(workDir, "obj_dir", fmt.Sprintf("V%s_mocked", moduleName)),
		workDir:    workDir,
		moduleName: moduleName,
		module:     module,
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
	testbench := generateVerilatorTestbench(sim.moduleName, sim.module)
	if err := os.WriteFile(testbenchPath, []byte(testbench), 0644); err != nil {
		return fmt.Errorf("failed to write Verilator testbench: %v", err)
	}

	// Create the obj_dir in the worker directory
	objDir := filepath.Join(sim.workDir, "obj_dir")
	if err := os.MkdirAll(objDir, 0755); err != nil {
		return fmt.Errorf("failed to create obj_dir: %v", err)
	}

	// Build verilator command with all SV files and parameters
	verilatorArgs := []string{
		"--cc", "--exe", "--build", "-Mdir", "obj_dir",
		"--timing", // Add timing option to handle delays
		"verilator_testbench.cpp",
	}

	// Add module files
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

// VerilatorTestbenchData contains data for the testbench template
type VerilatorTestbenchData struct {
	ModuleName string
	Inputs     []verilog.Port
	Outputs    []verilog.Port
	HasModule  bool
}

// generateVerilatorTestbench creates a C++ testbench that accepts file paths as command-line arguments
func generateVerilatorTestbench(moduleName string, module *verilog.Module) string {
	// Prepare template data
	templateData := VerilatorTestbenchData{
		ModuleName: moduleName,
		HasModule:  (module != nil),
	}

	// If we have module info, categorize ports
	if module != nil {
		for _, port := range module.Ports {
			if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
				templateData.Inputs = append(templateData.Inputs, port)
			}
			if port.Direction == verilog.OUTPUT || port.Direction == verilog.INOUT {
				templateData.Outputs = append(templateData.Outputs, port)
			}
		}
	}

	tmplText := `
#include <verilated.h>
#include "V{{.ModuleName}}_mocked.h"
#include <fstream>
#include <iostream>
#include <iomanip>  // For std::setw, std::setfill
#include <cstdint>
#include <string>
#include <map>
#include <vector>
#include <filesystem>

namespace fs = std::filesystem;

// Helper function to write output values cleanly
template<typename T>
void writeOutputValue(std::ofstream& outFile, T value, bool isBinary, int width = 0) {
    if (isBinary) {
        // For binary (1-bit) values
        outFile << (value ? '1' : '0');
    } else {
        // For multi-bit values, format as hex with proper width
        outFile << std::hex << std::setfill('0');
        if (width > 0) {
            outFile << std::setw(width) << static_cast<uint64_t>(value);
        } else {
            outFile << static_cast<uint64_t>(value);
        }
    }
    outFile << std::endl; // Ensure proper line ending
}

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
        
        // Apply the value to the appropriate port based on name
        {{if .HasModule}}
        // Use dynamic port handling for this module
        {{range .Inputs}}
        if (portName == "{{.Name}}") {
            {{if eq .Width 1}}
            dut->{{.Name}} = (valueStr[0] == '1' ? 1 : 0);
            {{else}}
            dut->{{.Name}} = std::stoull(valueStr, nullptr, 16);
            {{end}}
        } else 
        {{end}}
        {{else}}
        // Generic approach - handle common ports
        if (portName == "clk_i" || portName.find("clk") == 0) {
            dut->clk_i = (valueStr[0] == '1' ? 1 : 0);
        } else if (portName == "rst_ni" || portName == "rst_n") {
            dut->rst_ni = (valueStr[0] == '1' ? 1 : 0);
        } else if (portName.find("valid") != std::string::npos) {
            // Try to set any valid signal
            try {
                if (portName == "in_valid_i") dut->in_valid_i = (valueStr[0] == '1' ? 1 : 0);
                // Add other valid signals as needed
            } catch (...) {
                std::cerr << "Error setting valid signal: " << portName << std::endl;
            }
        } else 
        {{end}}
        {
            std::cerr << "Warning: Unknown input port: " << portName << std::endl;
        }
    }
    
    // Evaluate the model
    dut->eval();
    
    // Write outputs to the specified paths
    for (const auto& output : outputPaths) {
        const std::string& portName = output.first;
        const std::string& filePath = output.second;
        
        std::ofstream outFile(filePath, std::ios::out | std::ios::trunc);
        if (!outFile.is_open()) {
            std::cerr << "Error opening output file: " << filePath << std::endl;
            continue;
        }
        
        // Handle output ports
        {{if .HasModule}}
        // Use dynamic port handling for this module
        {{range .Outputs}}
        if (portName == "{{.Name}}") {
            {{if eq .Width 1}}
            writeOutputValue(outFile, dut->{{.Name}}, true);
            {{else}}
            writeOutputValue(outFile, dut->{{.Name}}, false, ({{.Width}}+3)/4);
            {{end}}
        } else 
        {{end}}
        {{else}}
        // Generic fallback approach
        if (portName == "out_valid_o") {
            writeOutputValue(outFile, dut->out_valid_o, true);
        } else if (portName == "out_addr_o") {
            writeOutputValue(outFile, dut->out_addr_o, false, 8);
        } else 
        {{end}}
        {
            std::cerr << "Warning: Unknown output port: " << portName << std::endl;
            outFile << "0" << std::endl; // Write default value
        }
        
        outFile.flush(); // Ensure all data is written
        outFile.close();
    }
    
    // Clean up
    delete dut;
    return 0;
}
`

	tmpl := template.Must(template.New("verilator_tb").Parse(tmplText))
	var buf bytes.Buffer
	tmpl.Execute(&buf, templateData)
	return buf.String()
}
