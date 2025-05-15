package simulator

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"

	"github.com/toby-bro/pfuzz/pkg/utils"
)

// IVerilogSimulator represents the IVerilog simulator
type IVerilogSimulator struct {
	execPath string
	workDir  string
	debug    *utils.DebugLogger
}

func TestIVerilogTool() error {
	cmd := exec.Command("iverilog", "-V")
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	if err := cmd.Run(); err != nil {
		cmd = exec.Command("iverilog")
		stderr.Reset()
		cmd.Stderr = &stderr
		if errSimple := cmd.Run(); errSimple != nil &&
			!strings.Contains(stderr.String(), "Usage:") {
			return fmt.Errorf(
				"iverilog basic check failed, check installation/PATH: %v - %s",
				errSimple,
				stderr.String(),
			)
		}
	}
	return nil
}

// NewIVerilogSimulator creates a new IVerilog simulator instance
func NewIVerilogSimulator(workDir string, verbose int) *IVerilogSimulator {
	return &IVerilogSimulator{
		execPath: filepath.Join(workDir, "module_sim_iv"),
		workDir:  workDir,
		debug:    utils.NewDebugLogger(verbose),
	}
}

// Compile compiles the verilog files with IVerilog
func (sim *IVerilogSimulator) Compile() error {
	return sim.CompileSpecific()
}

// CompileSpecific compiles only the specified files (or all .sv files if nil)
func (sim *IVerilogSimulator) CompileSpecific() error {
	sim.debug.Debug("Starting IVerilog compile in %s", sim.workDir)

	// Compile directly in the work directory
	cmdArgs := []string{"-o", "module_sim_iv", "-g2012", "-gsupported-assertions", "testbench.sv"}
	sim.debug.Debug("Running iverilog command: iverilog %s in directory %s",
		strings.Join(cmdArgs, " "), sim.workDir)

	cmd := exec.Command("iverilog", cmdArgs...)
	cmd.Dir = sim.workDir
	var stderr bytes.Buffer
	var stdout bytes.Buffer
	cmd.Stderr = &stderr
	cmd.Stdout = &stdout

	if err := cmd.Run(); err != nil {
		sim.debug.Debug("iverilog command failed: %v", err)
		sim.debug.Debug("stderr: %s", stderr.String())
		return fmt.Errorf("iverilog compilation failed: %v - %s", err, stderr.String())
	}
	if stdout.Len() > 0 {
		sim.debug.Debug("iverilog stdout: %s", stdout.String())
	}

	// Check if executable was created
	execPath := filepath.Join(sim.workDir, "module_sim_iv")
	sim.debug.Debug("Checking for compiled executable at %s", execPath)
	_, err := os.Stat(execPath)
	if err != nil {
		if os.IsNotExist(err) {
			// List the directory contents to debug
			files, _ := os.ReadDir(sim.workDir)
			fileList := make([]string, 0, len(files))
			for _, f := range files {
				fileList = append(fileList, f.Name())
			}
			sim.debug.Debug("Directory contents: %v", fileList)
			return fmt.Errorf(
				"executable not created at: %s (directory exists: %v)",
				execPath,
				true,
			)
		}
		return fmt.Errorf("error checking executable: %v", err)
	}

	// Make sure the executable has the right permissions
	if err := os.Chmod(execPath, 0o755); err != nil {
		return fmt.Errorf("failed to set executable permissions: %v", err)
	}

	return nil
}

// RunTest runs the simulator with the provided input directory and output paths
func (sim *IVerilogSimulator) RunTest(inputDir string, outputPaths map[string]string) error {
	// Make sure input and output directories exist
	if _, err := os.Stat(inputDir); os.IsNotExist(err) {
		return fmt.Errorf("input directory does not exist: %s", inputDir)
	}

	// Make sure input directory contains input files
	inputFiles, err := filepath.Glob(filepath.Join(inputDir, "input_*.hex"))
	if err != nil || len(inputFiles) == 0 {
		return fmt.Errorf("no input files found in: %s", inputDir)
	}

	// Copy input files to work directory
	for _, inputFile := range inputFiles {
		filename := filepath.Base(inputFile)
		destPath := filepath.Join(sim.workDir, filename)
		if err := utils.CopyFile(inputFile, destPath); err != nil {
			return fmt.Errorf("failed to copy input file %s: %v", filename, err)
		}
	}

	// Verify that the executable exists
	if _, err := os.Stat(sim.execPath); os.IsNotExist(err) {
		return fmt.Errorf("iverilog executable not found at: %s", sim.execPath)
	}

	// Run the simulation
	relExecPath := filepath.Base(sim.execPath)
	cmd := exec.Command("vvp", relExecPath)
	cmd.Dir = sim.workDir
	var stderr bytes.Buffer
	var stdout bytes.Buffer
	cmd.Stderr = &stderr
	cmd.Stdout = &stdout

	if err := cmd.Run(); err != nil {
		sim.debug.Debug("vvp execution failed with error: %v", err)
		sim.debug.Debug("stderr: %s", stderr.String())
		sim.debug.Debug("stdout: %s", stdout.String())
		return fmt.Errorf("iverilog execution failed: %v - %s", err, stderr.String())
	}

	// sim.debug.Printf("Simulation completed successfully")

	// Wait to ensure file system has completed writing
	// time.Sleep(50 * time.Millisecond)

	// Copy output files to their expected paths with the iv_ prefix
	for portName, outputPath := range outputPaths {
		srcPath := filepath.Join(sim.workDir, fmt.Sprintf("output_%s.hex", portName))
		if _, err := os.Stat(srcPath); os.IsNotExist(err) {
			return fmt.Errorf("output file not created for port %s", portName)
		}

		if err := utils.CopyFile(srcPath, outputPath); err != nil {
			return fmt.Errorf("failed to copy output file %s: %v", portName, err)
		}
	}

	return nil
}
