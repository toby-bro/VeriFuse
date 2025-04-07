package simulator

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"

	"github.com/toby-bro/pfuzz/internal/testgen"
	"github.com/toby-bro/pfuzz/internal/verilog"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

// VerilatorSimulator represents the Verilator simulator
type VerilatorSimulator struct {
	execPath   string
	workDir    string
	moduleName string
	module     *verilog.Module
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

	// Create the obj_dir in the worker directory
	objDir := filepath.Join(sim.workDir, "obj_dir")
	if err := os.MkdirAll(objDir, 0755); err != nil {
		return fmt.Errorf("failed to create obj_dir: %v", err)
	}

	// IMPORTANT: Check for the C++ testbench file, copy it from tmp_gen if needed
	testbenchPath := filepath.Join(sim.workDir, "testbench.cpp")
	if _, err := os.Stat(testbenchPath); os.IsNotExist(err) {
		// The testbench.cpp is not in the working directory, copy it from tmp_gen
		srcTestbench := filepath.Join(utils.TMP_DIR, "testbench.cpp")
		if _, err := os.Stat(srcTestbench); os.IsNotExist(err) {
			// If it doesn't exist in tmp_gen either, generate it if we have module info
			if sim.module != nil {
				gen := testgen.NewGenerator(sim.module)
				if err := gen.GenerateTestbenches(); err != nil {
					return fmt.Errorf("failed to generate testbenches: %v", err)
				}
			} else {
				return fmt.Errorf("testbench.cpp not found and module info not available")
			}
		}

		// Now copy from tmp_gen to the working directory
		if err := utils.CopyFile(srcTestbench, testbenchPath); err != nil {
			return fmt.Errorf("failed to copy testbench.cpp to working directory: %v", err)
		}
	}

	// Verify the testbench file exists and has content
	if info, err := os.Stat(testbenchPath); err != nil || info.Size() == 0 {
		return fmt.Errorf("testbench.cpp is missing or empty in %s", sim.workDir)
	}

	// Build verilator command with all SV files and parameters
	verilatorArgs := []string{
		"--cc", "--exe", "--build", "-Mdir", "obj_dir",
		"--timing", // Add timing option to handle delays
		"testbench.cpp",
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

	// Verify the executable was created
	execPath := sim.GetExecPath()
	if _, err := os.Stat(execPath); os.IsNotExist(err) {
		return fmt.Errorf("verilator executable not created at %s", execPath)
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
	if err := verifyOutputs(outputPaths); err != nil {
		return err
	}

	return nil
}

// verifyOutputs checks that all output files exist
func verifyOutputs(outputPaths map[string]string) error {
	for portName, outputPath := range outputPaths {
		if _, err := os.Stat(outputPath); os.IsNotExist(err) {
			return fmt.Errorf("output file was not created: %s for port %s", outputPath, portName)
		}
	}
	return nil
}

// GetExecPath returns the path to the compiled simulator executable
func (sim *VerilatorSimulator) GetExecPath() string {
	return sim.execPath
}
