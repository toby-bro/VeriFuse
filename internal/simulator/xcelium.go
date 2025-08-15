package simulator

import (
	"bytes"
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"

	"github.com/toby-bro/pfuzz/pkg/utils"
	"github.com/toby-bro/pfuzz/pkg/verilog"
)

var xceliumSemaphore = make(chan struct{}, 3)

// XCeliumSimulator represents the XCelium simulator
type XCeliumSimulator struct {
	workDir    string
	debug      *utils.DebugLogger
	svFileName string
}

func (sim *XCeliumSimulator) Type() Type {
	return XCELIUM
}

func (sim *XCeliumSimulator) DumpOptimisations() string {
	return ""
}

func TestXCeliumTool() error {
	cmd := exec.Command("xrun", "-version")
	var stderr bytes.Buffer
	cmd.Stderr = &stderr

	xceliumSemaphore <- struct{}{}
	defer func() { <-xceliumSemaphore }()

	if err := cmd.Run(); err != nil {
		return fmt.Errorf(
			"xrun basic check failed, check installation/PATH: %v",
			err,
		)
	}
	return nil
}

// NewXCeliumSimulator creates a new XCelium simulator instance
func NewXCeliumSimulator(
	actualWorkDir string,
	svFile *verilog.VerilogFile,
	verbose int,
) *XCeliumSimulator {
	return &XCeliumSimulator{
		workDir:    actualWorkDir,
		debug:      utils.NewDebugLogger(verbose),
		svFileName: svFile.Name,
	}
}

func (sim *XCeliumSimulator) Compile(ctx context.Context) error {
	sim.debug.Debug("Ensuring XCelium simulation directory exists: %s", sim.workDir)
	if err := os.MkdirAll(sim.workDir, 0o755); err != nil {
		return fmt.Errorf("failed to create xcelium work dir %s: %v", sim.workDir, err)
	}

	// acquire semaphore to limit concurrent XCelium runs or wait until one is available
	xceliumSemaphore <- struct{}{}
	defer func() { <-xceliumSemaphore }()

	sim.debug.Debug("Starting XCelium compile in %s", sim.workDir)

	cmdArgs := []string{
		"-elaborate",
		"../" + sim.svFileName,
	}
	sim.debug.Debug("Running xrun command: xrun %s in directory %s",
		strings.Join(cmdArgs, " "), sim.workDir)

	cmd := exec.Command("xrun", cmdArgs...)
	cmd.Dir = sim.workDir
	var stderr bytes.Buffer
	var stdout bytes.Buffer
	cmd.Stderr = &stderr
	cmd.Stdout = &stdout

	if err := cmd.Start(); err != nil {
		return fmt.Errorf("xrun compilation failed to start: %v", err)
	}

	done := make(chan error, 1)
	go func() {
		done <- cmd.Wait()
	}()

	select {
	case err := <-done:
		if err != nil {
			return fmt.Errorf(
				"xrun compilation failed: %v - stdout: %s, stderr: %s",
				err,
				stdout.String(),
				stderr.String(),
			)
		}
	case <-ctx.Done():
		// Context was cancelled (timeout or cancellation)
		if cmd.Process != nil {
			if err := cmd.Process.Kill(); err != nil {
				sim.debug.Debug("Failed to kill xrun process: %v", err)
			}
		}
		return fmt.Errorf("xrun compilation timed out or was cancelled: %v", ctx.Err())
	}
	if stdout.Len() > 0 {
		sim.debug.Debug("xrun stdout: %s", stdout.String())
	}

	return nil
}

func (sim *XCeliumSimulator) FailedCuzUnsupportedFeature(_ error) (bool, error) {
	return false, nil
}

// RunTest runs the simulator with the provided input directory and output paths
func (sim *XCeliumSimulator) RunTest(
	ctx context.Context,
	inputDir string,
	outputPaths map[*verilog.Port]string,
) error {
	// Make sure input directory and files exist (inputDir is the original source of inputs)
	if _, err := os.Stat(inputDir); os.IsNotExist(err) {
		return fmt.Errorf("input directory does not exist: %s", inputDir)
	}

	inputFiles, err := filepath.Glob(filepath.Join(inputDir, "input_*.hex"))
	if err != nil || len(inputFiles) == 0 {
		return fmt.Errorf("no input files found in: %s", inputDir)
	}

	for _, inputFile := range inputFiles {
		filename := filepath.Base(inputFile)
		destPath := filepath.Join(sim.workDir, filename)
		if err := utils.CopyFile(inputFile, destPath); err != nil {
			return fmt.Errorf("failed to copy input file %s: %v", filename, err)
		}
	}

	sourceTestbenchFile := filepath.Join("..", "testbench.sv")

	cmdArgs := []string{
		sourceTestbenchFile,
		"../" + sim.svFileName,
	}
	sim.debug.Debug("Running xrun command: xrun %s in directory %s",
		strings.Join(cmdArgs, " "), sim.workDir)

	xceliumSemaphore <- struct{}{}
	defer func() { <-xceliumSemaphore }()

	cmd := exec.Command("xrun", cmdArgs...)
	cmd.Dir = sim.workDir
	var stderr bytes.Buffer
	var stdout bytes.Buffer
	cmd.Stderr = &stderr
	cmd.Stdout = &stdout

	// Run with context timeout
	if err := cmd.Start(); err != nil {
		return fmt.Errorf("xcelium execution failed to start: %v", err)
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
			return fmt.Errorf("xcelium execution failed: %v - %s", err, stderr.String())
		}
	case <-ctx.Done():
		// Context was cancelled (timeout or cancellation)
		if cmd.Process != nil {
			if cmd.Process.Kill() != nil {
				sim.debug.Debug("Failed to kill vvp process: %v", cmd.Process.Kill())
			}
		}
		return fmt.Errorf("xcelium execution timed out or was cancelled: %v", ctx.Err())
	}

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
