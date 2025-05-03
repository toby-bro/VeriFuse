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

// NewIVerilogSimulator creates a new IVerilog simulator instance
func NewIVerilogSimulator(workDir string, verbose bool) *IVerilogSimulator {
	return &IVerilogSimulator{
		execPath: filepath.Join(workDir, "module_sim_iv"),
		workDir:  workDir,
		debug:    utils.NewDebugLogger(verbose),
	}
}

// Compile compiles the verilog files with IVerilog
func (sim *IVerilogSimulator) Compile() error {
	return sim.CompileSpecific(nil)
}

// CompileSpecific compiles only the specified files (or all .sv files if nil)
func (sim *IVerilogSimulator) CompileSpecific(specificFiles []string) error {
	sim.debug.Printf("Starting IVerilog compile in %s", sim.workDir)

	var fileNames []string

	if specificFiles == nil || len(specificFiles) == 0 {
		// Look for all Verilog files in the work directory
		files, err := filepath.Glob(filepath.Join(sim.workDir, "*.sv"))
		if err != nil {
			return fmt.Errorf("failed to find Verilog files: %v", err)
		}

		if len(files) == 0 {
			return fmt.Errorf("no Verilog files found in %s", sim.workDir)
		}

		// Get just the filenames for the command
		fileNames = make([]string, 0, len(files))
		for _, f := range files {
			fileNames = append(fileNames, filepath.Base(f))
		}
	} else {
		// Use the specified files
		fileNames = make([]string, len(specificFiles))
		for i, f := range specificFiles {
			fileNames[i] = filepath.Base(f)
		}
	}

	// Compile directly in the work directory
	cmdArgs := []string{"-o", "module_sim_iv", "-g2012", "-gsupported-assertions", "testbench.sv"}
	sim.debug.Printf("Running iverilog command: iverilog %s in directory %s",
		strings.Join(cmdArgs, " "), sim.workDir)

	cmd := exec.Command("iverilog", cmdArgs...)
	cmd.Dir = sim.workDir
	var stderr bytes.Buffer
	var stdout bytes.Buffer
	cmd.Stderr = &stderr
	cmd.Stdout = &stdout

	if err := cmd.Run(); err != nil {
		sim.debug.Printf("iverilog command failed: %v", err)
		sim.debug.Printf("stderr: %s", stderr.String())
		return fmt.Errorf("iverilog compilation failed: %v - %s", err, stderr.String())
	}
	if stdout.Len() > 0 {
		sim.debug.Printf("iverilog stdout: %s", stdout.String())
	}

	// Check if executable was created
	execPath := filepath.Join(sim.workDir, "module_sim_iv")
	sim.debug.Printf("Checking for compiled executable at %s", execPath)
	_, err := os.Stat(execPath)
	if err != nil {
		if os.IsNotExist(err) {
			// List the directory contents to debug
			files, _ := os.ReadDir(sim.workDir)
			fileList := make([]string, 0, len(files))
			for _, f := range files {
				fileList = append(fileList, f.Name())
			}
			sim.debug.Printf("Directory contents: %v", fileList)
			return fmt.Errorf("executable not created at: %s (directory exists: %v)", execPath, true)
		}
		return fmt.Errorf("error checking executable: %v", err)
	}

	// Make sure the executable has the right permissions
	if err := os.Chmod(execPath, 0755); err != nil {
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
		sim.debug.Printf("vvp execution failed with error: %v", err)
		sim.debug.Printf("stderr: %s", stderr.String())
		sim.debug.Printf("stdout: %s", stdout.String())
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
