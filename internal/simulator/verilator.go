package simulator

import (
	"bytes"
	"fmt"
	"log"
	"os"
	"os/exec"
	"path/filepath"

	"github.com/jns/pfuzz/pkg/utils"
)

// VerilatorSimulator represents the Verilator simulator
type VerilatorSimulator struct {
	execPath string
	workDir  string
}

// NewVerilatorSimulator creates a new Verilator simulator instance
func NewVerilatorSimulator(workDir string) *VerilatorSimulator {
	return &VerilatorSimulator{
		execPath: filepath.Join(workDir, "obj_dir", "Vibex_branch_predict_mocked"),
		workDir:  workDir,
	}
}

// Compile compiles the verilog files with Verilator
func (sim *VerilatorSimulator) Compile() error {
	// First check if the file already exists in the work directory
	workerVerilogPath := filepath.Join(sim.workDir, "ibex_branch_predict_mocked.sv")

	// If not, try to copy from tmp_gen
	if _, err := os.Stat(workerVerilogPath); os.IsNotExist(err) {
		verilogPath := filepath.Join(utils.TMP_DIR, "ibex_branch_predict_mocked.sv")
		if _, err := os.Stat(verilogPath); os.IsNotExist(err) {
			return fmt.Errorf("verilog file not found at %s", verilogPath)
		}

		if err := utils.CopyFile(verilogPath, workerVerilogPath); err != nil {
			return fmt.Errorf("failed to copy Verilog file: %v", err)
		}
	}

	// Create Verilator testbench
	testbenchPath := filepath.Join(sim.workDir, "verilator_testbench.cpp")

	// Create a testbench that takes file paths as command-line arguments
	testbench := generateVerilatorTestbench()
	if err := os.WriteFile(testbenchPath, []byte(testbench), 0644); err != nil {
		return fmt.Errorf("failed to write Verilator testbench: %v", err)
	}

	// Create the obj_dir in the worker directory
	objDir := filepath.Join(sim.workDir, "obj_dir")
	if err := os.MkdirAll(objDir, 0755); err != nil {
		return fmt.Errorf("failed to create obj_dir: %v", err)
	}

	// Run Verilator in the worker directory
	cmd := exec.Command("verilator", "--cc", "--exe", "--build", "-Mdir", "obj_dir",
		"ibex_branch_predict_mocked.sv", "verilator_testbench.cpp")
	cmd.Dir = sim.workDir

	var stderr bytes.Buffer
	cmd.Stderr = &stderr

	err := cmd.Run()
	if err != nil {
		log.Printf("Verilator error: %s\n%s", err, stderr.String())
		return fmt.Errorf("verilator compilation failed: %v", err)
	}

	return nil
}

// RunTest runs the simulator with specific input and output files
func (sim *VerilatorSimulator) RunTest(inputPath, pcPath, validPath, takenPath, targetPath string) error {
	// Get absolute paths
	absInputPath, _ := filepath.Abs(inputPath)
	absPcPath, _ := filepath.Abs(pcPath)
	absValidPath, _ := filepath.Abs(validPath)
	absTakenPath, _ := filepath.Abs(takenPath)
	absTargetPath, _ := filepath.Abs(targetPath)

	// Run the simulator with file paths as arguments
	cmd := exec.Command(sim.execPath,
		"--input="+absInputPath,
		"--pc="+absPcPath,
		"--valid="+absValidPath,
		"--taken="+absTakenPath,
		"--target="+absTargetPath)

	var stderr bytes.Buffer
	cmd.Stderr = &stderr

	if err := cmd.Run(); err != nil {
		return fmt.Errorf("verilator execution failed: %v - %s", err, stderr.String())
	}

	// Verify output files were created
	return VerifyOutputFiles(takenPath, targetPath)
}

// GetExecPath returns the path to the compiled simulator executable
func (sim *VerilatorSimulator) GetExecPath() string {
	return sim.execPath
}

// generateVerilatorTestbench creates a C++ testbench that accepts file paths as command-line arguments
func generateVerilatorTestbench() string {
	return `
#include <verilated.h>
#include "Vibex_branch_predict_mocked.h"
#include <fstream>
#include <iostream>
#include <cstdint>
#include <string>

int main(int argc, char** argv) {
    // Parse command line for files
    Verilated::commandArgs(argc, argv);
    
    std::string input_path, pc_path, valid_path, taken_path, target_path;
    
    // Process command line args for filenames
    for (int i = 1; i < argc; i++) {
        std::string arg = argv[i];
        if (arg.find("--input=") == 0) {
            input_path = arg.substr(8);
        } else if (arg.find("--pc=") == 0) {
            pc_path = arg.substr(5);
        } else if (arg.find("--valid=") == 0) {
            valid_path = arg.substr(8);
        } else if (arg.find("--taken=") == 0) {
            taken_path = arg.substr(8);
        } else if (arg.find("--target=") == 0) {
            target_path = arg.substr(9);
        }
    }
    
    if (input_path.empty() || pc_path.empty() || valid_path.empty() || 
        taken_path.empty() || target_path.empty()) {
        std::cerr << "Error: Missing required file paths" << std::endl;
        return 1;
    }
    
    // Create and initialize the model
    Vibex_branch_predict_mocked* dut = new Vibex_branch_predict_mocked;
    
    // Read input values
    std::ifstream input_file(input_path);
    std::ifstream pc_file(pc_path);
    std::ifstream valid_file(valid_path);
    
    if (!input_file || !pc_file || !valid_file) {
        std::cerr << "Error: Failed to open input files" << std::endl;
        delete dut;
        return 1;
    }
    
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
    std::ofstream taken_file(taken_path);
    std::ofstream target_file(target_path);
    
    if (!taken_file || !target_file) {
        std::cerr << "Error: Failed to open output files" << std::endl;
        delete dut;
        return 1;
    }
    
    taken_file << (int)dut->predict_branch_taken_o;
    target_file << std::hex << dut->predict_branch_pc_o;
    
    // Clean up
    taken_file.close();
    target_file.close();
    delete dut;
    
    return 0;
}
`
}
