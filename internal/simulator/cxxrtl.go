package simulator

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"syscall"
	"time"

	"github.com/toby-bro/pfuzz/internal/synth"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

// CXXRTLSimulator represents the CXXRTL simulator
type CXXRTLSimulator struct {
	execPath                    string
	workDir                     string
	originalVerilogFileBaseName string // e.g., my_module.v
	moduleName                  string // Top module name, e.g., my_module
	cxxrtlIncludeDir            string // Path to CXXRTL runtime include directory
	useSlang                    bool   // Whether to use Slang with Yosys
	logger                      *utils.DebugLogger
}

// TestCXXRTLTool checks if Yosys and g++ are available.
func TestCXXRTLTool(withSlang bool) error {
	// Check for Yosys
	if synth.TestYosysTool() != nil {
		return errors.New("Yosys tool check failed. Ensure Yosys is installed and in PATH")
	}
	// Check for g++
	cmdGXX := exec.Command("g++", "--version")
	var stderrGXX bytes.Buffer
	cmdGXX.Stderr = &stderrGXX
	cmdGXX.Stdout = &stderrGXX
	if err := cmdGXX.Run(); err != nil {
		return fmt.Errorf(
			"g++ basic check failed. Ensure g++ is installed and in PATH: %v - %s",
			err,
			stderrGXX.String(),
		)
	}
	if !strings.Contains(stderrGXX.String(), "g++") { // Basic check for g++ output
		return fmt.Errorf("g++ --version did not return expected output: %s", stderrGXX.String())
	}
	if withSlang {
		if err := synth.TestSlangPlugin(); err != nil {
			return fmt.Errorf(
				"Slang plugin check failed. Ensure Slang is installed and available in Yosys: %v",
				err,
			)
		}
	}
	return nil
}

// NewCXXRTLSimulator creates a new CXXRTL simulator instance.
// workDir: directory for compilation and simulation.
// originalVerilogFileBaseName: basename of the original Verilog/SV file (e.g., "design.v").
// moduleName: name of the top-level Verilog module.
// cxxrtlIncludeDir: path to the CXXRTL runtime include directory (e.g., "/usr/local/share/cxxrtl/runtime").
// optimized: whether to use compiler optimizations.
// verbose: verbosity level for logging.
func NewCXXRTLSimulator(
	workDir string,
	originalVerilogFileBaseName string,
	moduleName string,
	cxxrtlIncludeDir string,
	useSlang bool, // Added useSlang parameter
	verbose int,
) *CXXRTLSimulator {
	return &CXXRTLSimulator{
		// execPath will be set after successful compilation
		workDir:                     workDir,
		originalVerilogFileBaseName: originalVerilogFileBaseName,
		moduleName:                  moduleName,
		cxxrtlIncludeDir:            cxxrtlIncludeDir,
		useSlang:                    useSlang, // Store useSlang
		logger:                      utils.NewDebugLogger(verbose),
	}
}

// killProcessGroup kills the process and its entire process group to ensure cleanup
func killProcessGroup(cmd *exec.Cmd) error {
	if cmd.Process == nil {
		return errors.New("process is nil")
	}

	// Kill the entire process group
	pgid, err := syscall.Getpgid(cmd.Process.Pid)
	if err != nil {
		// Fallback to killing just the process
		return cmd.Process.Kill()
	}

	// Kill the process group with SIGTERM first
	if err := syscall.Kill(-pgid, syscall.SIGTERM); err != nil {
		return fmt.Errorf("failed to kill process group %d: %v", pgid, err)
	}

	// Give it a moment to terminate gracefully
	time.Sleep(100 * time.Millisecond)

	// Force kill if still running
	if err := syscall.Kill(-pgid, syscall.SIGKILL); err != nil {
		return fmt.Errorf("failed to force kill process group %d: %v", pgid, err)
	}

	return nil
}

// timeoutWithForceKill implements a more aggressive timeout mechanism
func timeoutWithForceKill(ctx context.Context, cmd *exec.Cmd, operation string) error {
	// Set process group ID for proper cleanup
	if cmd.SysProcAttr == nil {
		cmd.SysProcAttr = &syscall.SysProcAttr{}
	}
	cmd.SysProcAttr.Setpgid = true

	if err := cmd.Start(); err != nil {
		return fmt.Errorf("failed to start %s: %v", operation, err)
	}

	done := make(chan error, 1)
	go func() {
		done <- cmd.Wait()
	}()

	select {
	case err := <-done:
		return err
	case <-ctx.Done():
		// Use aggressive process group killing
		if err := killProcessGroup(cmd); err != nil {
			return fmt.Errorf("failed to kill %s process group: %v", operation, err)
		}
		return fmt.Errorf("%s timed out: %v", operation, ctx.Err())
	}
}

// Compile converts the Verilog design to C++ using Yosys, then compiles
// it with the CXXRTL testbench using g++.
func (sim *CXXRTLSimulator) Compile(ctx context.Context) error {
	sim.logger.Debug(
		"Starting CXXRTL compilation in %s for module %s (UseSlang: %t)",
		sim.workDir,
		sim.moduleName,
		sim.useSlang,
	)

	// --- Step 1: Yosys - Convert Verilog to CXXRTL C++ ---
	yosysInputFile := filepath.Join("..", sim.originalVerilogFileBaseName) // Relative to workDir
	yosysOutputCCFile := sim.moduleName + ".cc"                            // Output in workDir

	var yosysScript string
	var cmdYosys *exec.Cmd
	if sim.useSlang {
		yosysScript = fmt.Sprintf(
			"read_slang %s --top %s; prep -top %s",
			yosysInputFile,
			sim.moduleName,
			sim.moduleName,
		)
	} else {
		yosysScript = fmt.Sprintf("read_verilog -sv %s; prep -top %s", yosysInputFile, sim.moduleName)
	}

	// Add combinational loop detection and breaking
	yosysScript += "; write_cxxrtl " + yosysOutputCCFile

	if sim.useSlang {
		cmdYosys = exec.Command("yosys", "-m", "slang", "-p", yosysScript)
	} else {
		cmdYosys = exec.Command("yosys", "-p", yosysScript)
	}

	sim.logger.Debug(
		"Running Yosys command: yosys -p \"%s\" in directory %s",
		yosysScript,
		sim.workDir,
	)
	cmdYosys.Dir = sim.workDir
	var stderrYosys bytes.Buffer
	cmdYosys.Stderr = &stderrYosys

	// Use improved timeout mechanism
	if err := timeoutWithForceKill(ctx, cmdYosys, "yosys conversion"); err != nil {
		return fmt.Errorf(
			"yosys conversion (%s) failed: %v - %s",
			cmdYosys,
			err,
			stderrYosys.String(),
		)
	}
	sim.logger.Debug("Yosys conversion successful. Output: %s", yosysOutputCCFile)

	// Verify Yosys output (.cc and .h files)
	generatedCCPath := filepath.Join(sim.workDir, yosysOutputCCFile)
	if _, err := os.Stat(generatedCCPath); os.IsNotExist(err) {
		return fmt.Errorf("yosys did not generate .cc file: %s", generatedCCPath)
	}

	// --- Step 2: g++ - Compile CXXRTL C++ code with testbench ---
	testbenchCppFile := "testbench.cpp" // Assumed to be in workDir
	executableName := sim.moduleName + "_cxxsim"
	sim.execPath = filepath.Join(sim.workDir, executableName)

	gxxArgs := []string{"-std=c++17"}
	gxxArgs = append(gxxArgs, "-O0")
	gxxArgs = append(gxxArgs, "-Wall", "-Wextra") // Common warning flags
	gxxArgs = append(gxxArgs, "-I"+sim.cxxrtlIncludeDir)
	gxxArgs = append(gxxArgs, "-I.") // For <moduleName>.h in workDir
	gxxArgs = append(gxxArgs, testbenchCppFile, "-o", executableName)

	sim.logger.Debug(
		"Running g++ command: g++ %s in directory %s",
		strings.Join(gxxArgs, " "),
		sim.workDir,
	)
	cmdGXX := exec.Command("g++", gxxArgs...)
	cmdGXX.Dir = sim.workDir
	var stderrGXX bytes.Buffer
	cmdGXX.Stderr = &stderrGXX

	// Use improved timeout mechanism for g++
	if err := timeoutWithForceKill(ctx, cmdGXX, "g++ compilation"); err != nil {
		return fmt.Errorf("g++ compilation failed: %v - %s", err, stderrGXX.String())
	}

	// Verify executable creation
	if _, err := os.Stat(sim.execPath); os.IsNotExist(err) {
		return fmt.Errorf("g++ did not create executable: %s", sim.execPath)
	}

	// Set executable permissions
	if err := os.Chmod(sim.execPath, 0o755); err != nil {
		return fmt.Errorf("failed to set executable permissions for %s: %v", sim.execPath, err)
	}

	sim.logger.Debug("CXXRTL compilation successful. Executable: %s", sim.execPath)
	return nil
}

// RunTest runs the compiled CXXRTL simulation.
// inputDir: directory containing input files (input_<port>.hex).
// outputPaths: map of port names to their expected output file paths.
func (sim *CXXRTLSimulator) RunTest(
	ctx context.Context,
	inputDir string,
	outputPaths map[string]string,
) error {
	sim.logger.Debug(
		"Starting CXXRTL RunTest. Executable: %s, InputDir: %s",
		sim.execPath,
		inputDir,
	)

	// Verify executable exists
	if _, err := os.Stat(sim.execPath); os.IsNotExist(err) {
		return fmt.Errorf(
			"cxxrtl executable not found at %s. Compile step might have failed",
			sim.execPath,
		)
	}

	// Copy input files to work directory
	if _, err := os.Stat(inputDir); os.IsNotExist(err) {
		return fmt.Errorf("input directory does not exist: %s", inputDir)
	}
	inputHexFiles, err := filepath.Glob(filepath.Join(inputDir, "input_*.hex"))
	if err != nil {
		return fmt.Errorf("error finding input files in %s: %v", inputDir, err)
	}
	// It's okay if there are no input files for modules with no inputs.
	// The testbench.cpp should handle missing files gracefully if inputs are expected.

	for _, inputFile := range inputHexFiles {
		filename := filepath.Base(inputFile)
		destPath := filepath.Join(sim.workDir, filename)
		sim.logger.Debug("Copying input file %s to %s", inputFile, destPath)
		if err := utils.CopyFile(inputFile, destPath); err != nil {
			return fmt.Errorf("failed to copy input file %s to %s: %v", filename, sim.workDir, err)
		}
	}

	// Run the simulation executable with improved timeout handling
	cmd := exec.Command("./" + filepath.Base(sim.execPath))
	cmd.Dir = sim.workDir
	var stdoutSim, stderrSim bytes.Buffer
	cmd.Stdout = &stdoutSim
	cmd.Stderr = &stderrSim

	sim.logger.Debug("Executing CXXRTL simulation: %s in %s", cmd.String(), sim.workDir)

	// Use improved timeout mechanism for simulation execution
	if err := timeoutWithForceKill(ctx, cmd, "cxxrtl simulation execution"); err != nil {
		sim.logger.Error(
			"CXXRTL simulation execution failed: %v\nStdout: %s\nStderr: %s",
			err,
			stdoutSim.String(),
			stderrSim.String(),
		)
		return fmt.Errorf(
			"cxxrtl simulation execution failed: %v\nstdout: %s\nstderr: %s",
			err,
			stdoutSim.String(),
			stderrSim.String(),
		)
	}

	sim.logger.Debug("CXXRTL simulation execution successful.\nStdout: %s", stdoutSim.String())
	if stderrSim.Len() > 0 {
		sim.logger.Warn("CXXRTL simulation stderr (non-fatal or warning):\n%s", stderrSim.String())
	}

	// Copy output files from work directory to their final destination paths
	for portName, outputPath := range outputPaths {
		srcPath := filepath.Join(sim.workDir, fmt.Sprintf("output_%s.hex", portName))
		sim.logger.Debug("Checking for output file %s for port %s", srcPath, portName)

		if _, err := os.Stat(srcPath); os.IsNotExist(err) {
			// List directory contents for debugging if output file is missing
			files, _ := os.ReadDir(sim.workDir)
			fileList := make([]string, 0, len(files))
			for _, f := range files {
				fileList = append(fileList, f.Name())
			}
			sim.logger.Error("Work directory %s contents after run: %v", sim.workDir, fileList)
			return fmt.Errorf(
				"output file not created by simulation for port %s at %s",
				portName,
				srcPath,
			)
		}

		// Ensure the destination directory exists
		outputDir := filepath.Dir(outputPath)
		if err := os.MkdirAll(outputDir, 0o755); err != nil {
			return fmt.Errorf("failed to create output directory %s: %v", outputDir, err)
		}

		sim.logger.Debug("Copying output file %s to %s", srcPath, outputPath)
		if err := utils.CopyFile(srcPath, outputPath); err != nil {
			return fmt.Errorf(
				"failed to copy output file for port %s from %s to %s: %v",
				portName,
				srcPath,
				outputPath,
				err,
			)
		}
	}

	sim.logger.Debug("CXXRTL RunTest completed successfully.")
	return nil
}
