package simulator

import (
	"bytes"
	"fmt"
	"log"
	"os"
	"os/exec"
	"path/filepath"
	"time"

	"github.com/jns/pfuzz/pkg/utils"
)

// VerilatorSimulator represents the Verilator simulator
type VerilatorSimulator struct {
	execPath string
}

// NewVerilatorSimulator creates a new Verilator simulator instance
func NewVerilatorSimulator() *VerilatorSimulator {
	return &VerilatorSimulator{
		execPath: filepath.Join(utils.TMP_DIR, "obj_dir", "Vibex_branch_predict_mocked"),
	}
}

// Compile compiles the verilog files with Verilator
func (sim *VerilatorSimulator) Compile() error {
	curDir, _ := os.Getwd()

	// Change to the tmp_gen directory to run Verilator
	origDir, _ := os.Getwd()
	if err := os.Chdir(filepath.Join(curDir, utils.TMP_DIR)); err != nil {
		return fmt.Errorf("failed to change directory: %v", err)
	}
	defer os.Chdir(origDir)

	// Run Verilator with the updated module name
	cmd := exec.Command("verilator", "--cc", "--exe", "--build", "-Mdir", "obj_dir",
		"ibex_branch_predict_mocked.sv", "testbench.cpp")

	var stderr bytes.Buffer
	cmd.Stderr = &stderr

	err := cmd.Run()
	if err != nil {
		log.Printf("Verilator error: %s\n%s", err, stderr.String())
	}

	return err
}

// Run runs the simulator with the given test case
func (sim *VerilatorSimulator) Run() error {
	// Check if the simulator binary exists
	if _, err := os.Stat(sim.execPath); os.IsNotExist(err) {
		return fmt.Errorf("simulator executable not found at %s", sim.execPath)
	}

	// Run the simulator
	cmd := exec.Command(sim.execPath)
	var stderr bytes.Buffer
	cmd.Stderr = &stderr

	err := cmd.Run()
	if err != nil {
		return fmt.Errorf("simulator execution failed: %v - %s", err, stderr.String())
	}

	// Verify output files were created and wait if needed
	return verifyOutputFiles()
}

// ReadResults reads the simulation results
func (sim *VerilatorSimulator) ReadResults() (SimResult, error) {
	return ReadSimResults()
}

// SimResult represents the results of a simulation run
type SimResult struct {
	BranchTaken uint8
	BranchPc    uint32
}

// ReadSimResults reads the simulation results from output files
func ReadSimResults() (SimResult, error) {
	// Try to read the taken.hex file
	takenPath := filepath.Join(utils.TMP_DIR, "taken.hex")
	taken, err := os.ReadFile(takenPath)
	if err != nil {
		return SimResult{}, fmt.Errorf("failed to read taken.hex: %v", err)
	}

	// Check if the file is empty
	if len(taken) == 0 {
		return SimResult{}, fmt.Errorf("taken.hex file is empty")
	}

	// Try to read the target.hex file
	targetPath := filepath.Join(utils.TMP_DIR, "target.hex")
	target, err := os.ReadFile(targetPath)
	if err != nil {
		return SimResult{}, fmt.Errorf("failed to read target.hex: %v", err)
	}

	// Check if the file is empty
	if len(target) == 0 {
		return SimResult{}, fmt.Errorf("target.hex file is empty")
	}

	// Parse the results
	var result SimResult
	result.BranchTaken = taken[0] - '0'

	var targetVal uint32
	_, err = fmt.Sscanf(string(target), "%x", &targetVal)
	if err != nil {
		return SimResult{}, fmt.Errorf("failed to parse target value: %v", err)
	}
	result.BranchPc = targetVal

	return result, nil
}

// Helper function to verify output files exist
func verifyOutputFiles() error {
	takenPath := filepath.Join(utils.TMP_DIR, "taken.hex")
	targetPath := filepath.Join(utils.TMP_DIR, "target.hex")

	// Try a few times with short delays in case files are still being written
	for i := 0; i < 3; i++ {
		// Check if both files exist and are non-empty
		if takenInfo, err := os.Stat(takenPath); err == nil && takenInfo.Size() > 0 {
			if targetInfo, err := os.Stat(targetPath); err == nil && targetInfo.Size() > 0 {
				return nil
			}
		}
		// Wait a bit and try again
		time.Sleep(100 * time.Millisecond)
	}

	return fmt.Errorf("output files were not created properly")
}
