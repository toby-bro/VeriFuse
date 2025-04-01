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
	cmd := exec.Command(sim.execPath)
	return cmd.Run()
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
	taken, err := os.ReadFile(filepath.Join(utils.TMP_DIR, "taken.hex"))
	if err != nil {
		return SimResult{}, err
	}

	target, err := os.ReadFile(filepath.Join(utils.TMP_DIR, "target.hex"))
	if err != nil {
		return SimResult{}, err
	}

	var result SimResult
	result.BranchTaken = taken[0] - '0'

	var targetVal uint32
	fmt.Sscanf(string(target), "%x", &targetVal)
	result.BranchPc = targetVal

	return result, nil
}
