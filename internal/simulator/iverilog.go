package simulator

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"

	"github.com/toby-bro/pfuzz/pkg/utils"
	"github.com/toby-bro/pfuzz/pkg/verilog"
)

// IVerilogSimulator represents the IVerilog simulator
type IVerilogSimulator struct {
	execPath   string
	workDir    string // This will be the dedicated subdirectory, e.g., baseWorkDir/iverilog_run
	debug      *utils.DebugLogger
	svFileName string // Name of the SystemVerilog file to compile
}

func (sim *IVerilogSimulator) Type() Type {
	return IVERILOG
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
func NewIVerilogSimulator(
	actualWorkDir string,
	svFile *verilog.VerilogFile,
	verbose int,
) *IVerilogSimulator {
	return &IVerilogSimulator{
		execPath:   filepath.Join(actualWorkDir, "module_sim_iv"),
		workDir:    actualWorkDir,
		debug:      utils.NewDebugLogger(verbose),
		svFileName: svFile.Name,
	}
}

// Compile compiles the verilog files with IVerilog
func (sim *IVerilogSimulator) Compile(ctx context.Context) error {
	sim.debug.Debug("Ensuring IVerilog simulation directory exists: %s", sim.workDir)
	if err := os.MkdirAll(sim.workDir, 0o755); err != nil {
		return fmt.Errorf("failed to create iverilog work dir %s: %v", sim.workDir, err)
	}

	sim.debug.Debug("Starting IVerilog compile in %s", sim.workDir)

	// Determine testbench file extension based on context
	// If working directory contains "sv2v", use .v testbench for Verilog compatibility
	sourceTestbenchFile := filepath.Join("..", "testbench.sv")

	// Compile directly in the work directory
	cmdArgs := []string{
		"-o",
		"module_sim_iv",
		"-g2012",
		"-gsupported-assertions",
		sourceTestbenchFile,
		"../" + sim.svFileName, // This is the main module file
	}
	sim.debug.Debug("Running iverilog command: iverilog %s in directory %s",
		strings.Join(cmdArgs, " "), sim.workDir)

	cmd := exec.Command("iverilog", cmdArgs...)
	cmd.Dir = sim.workDir
	var stderr bytes.Buffer
	var stdout bytes.Buffer
	cmd.Stderr = &stderr
	cmd.Stdout = &stdout

	// Run with context timeout
	if err := cmd.Start(); err != nil {
		return fmt.Errorf("iverilog compilation failed to start: %v", err)
	}

	// Wait for command completion or context cancellation
	done := make(chan error, 1)
	go func() {
		done <- cmd.Wait()
	}()

	select {
	case err := <-done:
		if err != nil {
			return fmt.Errorf("iverilog compilation failed: %v - %s", err, stderr.String())
		}
	case <-ctx.Done():
		// Context was cancelled (timeout or cancellation)
		if cmd.Process != nil {
			if err := cmd.Process.Kill(); err != nil {
				sim.debug.Debug("Failed to kill iverilog process: %v", err)
			}
		}
		return fmt.Errorf("iverilog compilation timed out or was cancelled: %v", ctx.Err())
	}
	if stdout.Len() > 0 {
		sim.debug.Debug("iverilog stdout: %s", stdout.String())
	}

	// Check if executable was created using sim.execPath
	sim.debug.Debug("Checking for compiled executable at %s", sim.execPath)
	_, err := os.Stat(sim.execPath)
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
				sim.execPath,
				true, // Assuming sim.workDir (parent of execPath) was created
			)
		}
		return fmt.Errorf("error checking executable: %v", err)
	}

	// Make sure the executable has the right permissions
	if err := os.Chmod(sim.execPath, 0o755); err != nil {
		return fmt.Errorf("failed to set executable permissions: %v", err)
	}

	return nil
}

var (
	iverilogUnsupportedPattern = `sorry: "\w+" expressions not supported yet|error: System function \$sampled not defined in system table or SFT file(s).`
	iverilogUnsupportedRegex   = regexp.MustCompile(iverilogUnsupportedPattern)
)

func (sim *IVerilogSimulator) FailedCuzUnsupportedFeature(log error) (bool, error) {
	if log == nil {
		return false, nil
	}
	if match := iverilogUnsupportedRegex.FindStringSubmatch(log.Error()); len(match) > 0 {
		return true, errors.New(match[0])
	}
	return false, nil
}

// RunTest runs the simulator with the provided input directory and output paths
func (sim *IVerilogSimulator) RunTest(
	ctx context.Context,
	inputDir string,
	outputPaths map[*verilog.Port]string,
) error {
	// Make sure input directory and files exist (inputDir is the original source of inputs)
	if _, err := os.Stat(inputDir); os.IsNotExist(err) {
		return fmt.Errorf("input directory does not exist: %s", inputDir)
	}

	// Make sure input directory contains input files
	inputFiles, err := filepath.Glob(filepath.Join(inputDir, "input_*.hex"))
	if err != nil || len(inputFiles) == 0 {
		return fmt.Errorf("no input files found in: %s", inputDir)
	}

	// Copy input files to work directory (sim.workDir is now the iverilog_run subdir)
	for _, inputFile := range inputFiles {
		filename := filepath.Base(inputFile)
		destPath := filepath.Join(sim.workDir, filename)
		if err := utils.CopyFile(inputFile, destPath); err != nil {
			return fmt.Errorf("failed to copy input file %s: %v", filename, err)
		}
	}

	// Verify that the executable exists (sim.execPath points into sim.workDir)
	if _, err := os.Stat(sim.execPath); os.IsNotExist(err) {
		return fmt.Errorf("iverilog executable not found at: %s", sim.execPath)
	}

	// Run the simulation from within sim.workDir
	// relExecPath will be "module_sim_iv"
	relExecPath := filepath.Base(sim.execPath)
	cmd := exec.Command("vvp", relExecPath)
	cmd.Dir = sim.workDir // Execute from the iverilog_run subdirectory
	var stderr bytes.Buffer
	var stdout bytes.Buffer
	cmd.Stderr = &stderr
	cmd.Stdout = &stdout

	// Run with context timeout
	if err := cmd.Start(); err != nil {
		return fmt.Errorf(
			"iverilog execution failed to start: %v, stdout: %s, stderr: %s",
			err,
			stdout.String(),
			stderr.String(),
		)
	}

	// Wait for command completion or context cancellation
	done := make(chan error, 1)
	go func() {
		done <- cmd.Wait()
	}()

	select {
	case err := <-done:
		if err != nil {
			sim.debug.Debug("vvp execution failed with error: %v", err)
			sim.debug.Debug("stderr: %s", stderr.String())
			sim.debug.Debug("stdout: %s", stdout.String())
			return fmt.Errorf("iverilog execution failed: %v", err)
		}
	case <-ctx.Done():
		// Context was cancelled (timeout or cancellation)
		if cmd.Process != nil {
			if cmd.Process.Kill() != nil {
				sim.debug.Debug("Failed to kill vvp process: %v", cmd.Process.Kill())
			}
		}
		return fmt.Errorf("iverilog execution timed out or was cancelled: %v", ctx.Err())
	}

	// sim.debug.Printf("Simulation completed successfully")

	// Wait to ensure file system has completed writing
	// time.Sleep(50 * time.Millisecond)

	// Copy output files from sim.workDir to their expected paths
	for port, outputPath := range outputPaths {
		srcPath := filepath.Join(sim.workDir, fmt.Sprintf("output_%s.hex", port.Name))
		if _, err := os.Stat(srcPath); os.IsNotExist(err) {
			return fmt.Errorf("output file not created for port %s in %s", port.Name, sim.workDir)
		}

		if err := utils.CopyFile(srcPath, outputPath); err != nil {
			return fmt.Errorf("failed to copy output file %s: %v", port.Name, err)
		}
	}

	return nil
}
