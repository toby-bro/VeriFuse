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
	workDir  string
}

// NewIVerilogSimulator creates a new IVerilog simulator instance
func NewIVerilogSimulator(workDir string) *IVerilogSimulator {
	// Create exec path in the worker directory
	return &IVerilogSimulator{
		execPath: filepath.Join(workDir, "ibex_sim_iv"),
		workDir:  workDir,
	}
}

// Compile compiles the verilog files with IVerilog
func (sim *IVerilogSimulator) Compile() error {
	// Get the absolute path to source files
	verilogPath := filepath.Join(utils.TMP_DIR, "ibex_branch_predict_mocked.sv")
	absVerilogPath, err := filepath.Abs(verilogPath)
	if err != nil {
		return fmt.Errorf("failed to get absolute path for verilog file: %v", err)
	}

	testbenchPath := filepath.Join(utils.TMP_DIR, "testbench.sv")
	absTestbenchPath, err := filepath.Abs(testbenchPath)
	if err != nil {
		return fmt.Errorf("failed to get absolute path for testbench: %v", err)
	}

	// Use the standard iverilog command that works for you
	cmd := exec.Command("iverilog", "-o", sim.execPath, absVerilogPath, absTestbenchPath, "-g2012")

	var stderr bytes.Buffer
	cmd.Stderr = &stderr

	if err := cmd.Run(); err != nil {
		return fmt.Errorf("iverilog compilation failed: %v - %s", err, stderr.String())
	}

	return nil
}

// RunTest runs the simulator with specific input and output files
func (sim *IVerilogSimulator) RunTest(inputPath, pcPath, validPath, takenPath, targetPath string) error {
	// Instead of generating a complex testbench with file paths, use a simpler approach
	// Copy the input files to the expected locations in tmp_gen
	tmpInputPath := filepath.Join(utils.TMP_DIR, "input.hex")
	tmpPcPath := filepath.Join(utils.TMP_DIR, "pc.hex")
	tmpValidPath := filepath.Join(utils.TMP_DIR, "valid.hex")
	tmpTakenPath := filepath.Join(utils.TMP_DIR, "taken.hex")
	tmpTargetPath := filepath.Join(utils.TMP_DIR, "target.hex")

	// Make sure any existing output files are removed first
	os.Remove(tmpTakenPath)
	os.Remove(tmpTargetPath)

	// Copy input files
	if err := utils.CopyFile(inputPath, tmpInputPath); err != nil {
		return fmt.Errorf("failed to copy input file: %v", err)
	}
	if err := utils.CopyFile(pcPath, tmpPcPath); err != nil {
		return fmt.Errorf("failed to copy PC file: %v", err)
	}
	if err := utils.CopyFile(validPath, tmpValidPath); err != nil {
		return fmt.Errorf("failed to copy valid file: %v", err)
	}

	// Run the simulation using the stock testbench
	cmd := exec.Command(sim.execPath)
	var stderr bytes.Buffer
	cmd.Stderr = &stderr

	if err := cmd.Run(); err != nil {
		return fmt.Errorf("iverilog execution failed: %v - %s", err, stderr.String())
	}

	// Copy output files back to their expected locations
	if err := utils.CopyFile(tmpTakenPath, takenPath); err != nil {
		return fmt.Errorf("failed to copy taken output: %v", err)
	}
	if err := utils.CopyFile(tmpTargetPath, targetPath); err != nil {
		return fmt.Errorf("failed to copy target output: %v", err)
	}

	return nil
}
