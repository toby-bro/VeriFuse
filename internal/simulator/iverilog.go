package simulator

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"

	"github.com/jns/pfuzz/pkg/utils"
)

// IVerilogSimulator represents the IVerilog simulator
type IVerilogSimulator struct {
	execPath string
}

// NewIVerilogSimulator creates a new IVerilog simulator instance
func NewIVerilogSimulator() *IVerilogSimulator {
	return &IVerilogSimulator{
		execPath: filepath.Join(utils.TMP_DIR, "ibex_sim_iv"),
	}
}

// Compile compiles the verilog files with IVerilog
func (sim *IVerilogSimulator) Compile() error {
	cmd := exec.Command("iverilog", "-o", sim.execPath, "-g2012",
		filepath.Join(utils.TMP_DIR, "ibex_branch_predict_mocked.sv"),
		filepath.Join(utils.TMP_DIR, "testbench.sv"))

	if err := cmd.Run(); err != nil {
		return fmt.Errorf("iverilog compilation failed: %v", err)
	}

	return nil
}

// Run runs the simulator with the given test case
func (sim *IVerilogSimulator) Run() error {
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

	// Verify output files were created
	return verifyOutputFiles()
}

// ReadResults reads the simulation results
func (sim *IVerilogSimulator) ReadResults() (SimResult, error) {
	return ReadSimResults()
}
