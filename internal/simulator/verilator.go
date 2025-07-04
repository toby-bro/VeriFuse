package simulator

import (
	"bytes"
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"syscall"
	"time"

	"github.com/toby-bro/pfuzz/pkg/utils"
	"github.com/toby-bro/pfuzz/pkg/verilog"
)

// VerilatorSimulator represents the Verilator simulator
type VerilatorSimulator struct {
	execPath   string
	workDir    string
	svFileName string
	module     *verilog.Module
	optimized  bool
	logger     *utils.DebugLogger
}

func TestVerilatorTool() error {
	cmd := exec.Command("verilator", "--version")
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	if err := cmd.Run(); err != nil {
		return fmt.Errorf(
			"verilator basic check failed, check installation/PATH: %v - %s",
			err,
			stderr.String(),
		)
	}
	return nil
}

// NewVerilatorSimulator creates a new Verilator simulator instance
func NewVerilatorSimulator(
	workDir string,
	svFile *verilog.VerilogFile,
	moduleName string,
	optimized bool,
	verbose int,
) *VerilatorSimulator {
	if _, exists := svFile.Modules[moduleName]; !exists {
		return nil
	}
	return &VerilatorSimulator{
		execPath:   filepath.Join(workDir, "obj_dir", "Vtestbench"),
		workDir:    workDir,
		svFileName: svFile.Name,
		module:     svFile.Modules[moduleName],
		optimized:  optimized,
		logger:     utils.NewDebugLogger(verbose),
	}
}

// killProcessGroup kills a process and its children using process groups
func (sim *VerilatorSimulator) killProcessGroup(cmd *exec.Cmd) error {
	if cmd.Process == nil {
		return nil
	}

	// Try SIGTERM first
	if err := syscall.Kill(-cmd.Process.Pid, syscall.SIGTERM); err != nil {
		// If SIGTERM fails, try SIGKILL on the process directly
		return cmd.Process.Kill()
	}

	// Wait a bit for graceful termination
	time.Sleep(100 * time.Millisecond)

	// Force kill with SIGKILL if process is still running
	if cmd.ProcessState == nil || !cmd.ProcessState.Exited() {
		if syscall.Kill(-cmd.Process.Pid, syscall.SIGKILL) != nil {
			// If SIGKILL fails, try killing the process directly
			if err := cmd.Process.Kill(); err != nil {
				return fmt.Errorf("failed to kill process group: %v", err)
			}
		}
	}

	return nil
}

// timeoutWithForceKill implements a more aggressive timeout mechanism
func (sim *VerilatorSimulator) timeoutWithForceKill(
	ctx context.Context,
	cmd *exec.Cmd,
	operation string,
) error {
	// Set up process group for better cleanup
	cmd.SysProcAttr = &syscall.SysProcAttr{Setpgid: true}

	if err := cmd.Start(); err != nil {
		return fmt.Errorf("failed to start %s: %v", operation, err)
	}

	done := make(chan error, 1)
	go func() {
		done <- cmd.Wait()
	}()

	select {
	case err := <-done:
		if err != nil {
			return fmt.Errorf("%s failed: %v", operation, err)
		}
		return nil
	case <-ctx.Done():
		if sim.killProcessGroup(cmd) != nil {
			sim.logger.Warn("Failed to kill process group for %s", operation)
		}
		return fmt.Errorf("%s timed out: %v", operation, ctx.Err())
	}
}

// Compile compiles the verilog files with Verilator
func (sim *VerilatorSimulator) Compile(ctx context.Context) error {
	// Create the obj_dir in the worker directory
	objDir := filepath.Join(sim.workDir, "obj_dir")
	if err := os.MkdirAll(objDir, 0o755); err != nil {
		return fmt.Errorf("failed to create obj_dir: %v", err)
	}

	// Determine testbench file extension based on context
	testbenchPath := filepath.Join(filepath.Dir(sim.workDir), "testbench.sv")

	// Verify the testbench file exists and has content
	if info, err := os.Stat(testbenchPath); err != nil || info.Size() == 0 {
		return fmt.Errorf(
			"testbench.sv is missing or empty in %s",
			filepath.Dir(sim.workDir),
		)
	}

	// Build verilator command with all SV files and parameters
	verilatorArgs := []string{
		"--binary", "--exe", "--build", "-Mdir", "obj_dir", "-sv",
		"--timing", // Add timing option to handle delays
		"--assert",
		"-Wno-CMPCONST",
		"-Wno-DECLFILENAME",
		"-Wno-MULTIDRIVEN",
		"-Wno-NOLATCH",
		"-Wno-LATCH", // added for the sv2v compatibility
		"-Wno-UNDRIVEN",
		"-Wno-UNOPTFLAT",
		"-Wno-UNUSED",
		"-Wno-UNSIGNED",
		"-Wno-WIDTHEXPAND",
		"-Wno-WIDTHTRUNC",
		"-Wno-MULTITOP",
		"-Wno-CASEINCOMPLETE",
		"-Wno-CASEOVERLAP",
		"-Wno-ASCRANGE",
		"-Wno-CASEX",
		"../testbench.sv",
		"../" + sim.svFileName,
	}

	if sim.optimized {
		verilatorArgs = append(verilatorArgs, "-O3")
	} else {
		verilatorArgs = append(verilatorArgs, "-O0")
	}

	// Run Verilator in the worker directory with improved timeout handling
	cmd := exec.Command("verilator", verilatorArgs...)
	cmd.Dir = sim.workDir

	var stderr bytes.Buffer
	cmd.Stderr = &stderr

	// Use improved timeout handling with process groups
	if err := sim.timeoutWithForceKill(ctx, cmd, "verilator compilation"); err != nil {
		// retry once on failure
		sim.logger.Warn(
			"[%s] Verilator compilation failed, retrying...",
			strings.Split(sim.workDir, "/")[1],
		)
		time.Sleep(10 * time.Millisecond)

		// Retry with timeout
		cmd = exec.Command("verilator", verilatorArgs...)
		cmd.Dir = sim.workDir
		cmd.Stderr = &stderr

		if retryErr := sim.timeoutWithForceKill(ctx, cmd, "verilator compilation retry"); retryErr != nil {
			return fmt.Errorf(
				"verilator compilation failed after retry: %v\n%s",
				retryErr,
				stderr.String(),
			)
		}
	}

	// Verify the executable was created
	execPath := sim.execPath
	if _, err := os.Stat(execPath); os.IsNotExist(err) {
		time.Sleep(10 * time.Millisecond)
		if _, err := os.Stat(execPath); os.IsNotExist(err) {
			return fmt.Errorf("verilator executable not created at %s", execPath)
		}
	}

	return nil
}

func (sim *VerilatorSimulator) FailedCuzUnsupportedFeature(_ error) (bool, error) {
	// Not implemented yet
	return false, nil
}

// RunTest runs the simulator with provided input directory and output paths
func (sim *VerilatorSimulator) RunTest(
	ctx context.Context,
	inputDir string,
	outputPaths map[*verilog.Port]string,
) error {
	// 1. Check input directory and files
	sim.logger.Debug("Verilator RunTest: Input directory: %s", inputDir)
	if _, err := os.Stat(inputDir); os.IsNotExist(err) {
		return fmt.Errorf("input directory does not exist: %s", inputDir)
	}
	inputFiles, err := filepath.Glob(filepath.Join(inputDir, "input_*.hex"))
	if err != nil {
		return fmt.Errorf("error finding input files in %s: %v", inputDir, err)
	}
	if len(inputFiles) == 0 {
		sim.logger.Warn("No input files (input_*.hex) found in: %s", inputDir)
	} else {
		sim.logger.Debug("Verilator RunTest: Found input files: %v", inputFiles)
	}

	// 2. Copy input files to work directory
	for _, inputFile := range inputFiles {
		filename := filepath.Base(inputFile)
		destPath := filepath.Join(sim.workDir, filename)
		sim.logger.Debug("Verilator RunTest: Copying input %s to %s", inputFile, destPath)
		if err := utils.CopyFile(inputFile, destPath); err != nil {
			return fmt.Errorf("failed to copy input file %s to %s: %v", filename, sim.workDir, err)
		}
	}

	// 3. Verify executable exists
	if _, err := os.Stat(sim.execPath); os.IsNotExist(err) {
		// Attempt to list contents of obj_dir for debugging
		objDirPath := filepath.Dir(sim.execPath)
		files, readErr := os.ReadDir(objDirPath)
		var fileList string
		if readErr == nil {
			names := make([]string, 0, len(files))
			for _, f := range files {
				names = append(names, f.Name())
			}
			fileList = fmt.Sprintf("%v", names)
		} else {
			fileList = fmt.Sprintf("error reading dir %s: %v", objDirPath, readErr)
		}
		sim.logger.Debug("Verilator RunTest: Contents of %s: %s", objDirPath, fileList)
		return fmt.Errorf("verilator executable not found at: %s", sim.execPath)
	}
	sim.logger.Debug("Verilator RunTest: Verified executable exists: %s", sim.execPath)

	// 4. Run the simulation executable with improved timeout handling
	relExecPath := filepath.Join(".", "obj_dir", "Vtestbench") // Use relative path
	sim.logger.Debug("Running Verilator command: %s in %s", relExecPath, sim.workDir)
	cmd := exec.Command(relExecPath)
	cmd.Dir = sim.workDir // Set the working directory for the command
	var stderr bytes.Buffer
	var stdout bytes.Buffer
	cmd.Stderr = &stderr
	cmd.Stdout = &stdout

	sim.logger.Debug(
		"Verilator command details: Path=%s, Dir=%s, Args=%v",
		cmd.Path,
		cmd.Dir,
		cmd.Args,
	)

	// Execute with improved timeout and process group handling
	if err := sim.timeoutWithForceKill(ctx, cmd, "verilator simulation execution"); err != nil {
		files, _ := os.ReadDir(sim.workDir)
		fileList := make([]string, 0, len(files))
		for _, f := range files {
			fileList = append(fileList, f.Name())
		}
		sim.logger.Debug("Work directory contents after failed run: %v", fileList)
		return fmt.Errorf(
			"verilator execution failed: %v\nstdout: %sstderr: %s",
			err,
			stdout.String(),
			stderr.String(),
		)
	}
	sim.logger.Debug("Verilator execution successful.")
	sim.logger.Debug(
		"Verilator execution stdout:\n%s",
		stdout.String(),
	) // Log stdout on success too
	if stderr.Len() > 0 {
		sim.logger.Error(
			"Verilator execution stderr (non-fatal):\n%s",
			stderr.String(),
		) // Log stderr even on success if not empty
	}

	// 5. Copy output files from work directory to expected paths
	sim.logger.Debug("Verilator RunTest: Copying output files. Expected outputs: %v", outputPaths)
	for port, outputPath := range outputPaths {
		srcPath := filepath.Join(sim.workDir, fmt.Sprintf("output_%s.hex", port.Name))
		sim.logger.Debug("Verilator RunTest: Checking for output file %s", srcPath)
		if _, err := os.Stat(srcPath); os.IsNotExist(err) {
			// List directory contents for debugging if output file is missing
			files, _ := os.ReadDir(sim.workDir)
			fileList := make([]string, 0, len(files))
			for _, f := range files {
				fileList = append(fileList, f.Name())
			}
			sim.logger.Debug("Work directory contents after run: %v", fileList)
			return fmt.Errorf(
				"output file not created by simulation for port %s at %s",
				port.Name,
				srcPath,
			)
		}
		sim.logger.Debug(
			"Verilator RunTest: Found output file %s. Copying to %s",
			srcPath,
			outputPath,
		)

		// Ensure the destination directory exists
		outputDir := filepath.Dir(outputPath)
		if err := os.MkdirAll(outputDir, 0o755); err != nil {
			return fmt.Errorf("failed to create output directory %s: %v", outputDir, err)
		}

		if err := utils.CopyFile(srcPath, outputPath); err != nil {
			return fmt.Errorf(
				"failed to copy output file for port %s from %s to %s: %v",
				port.Name,
				srcPath,
				outputPath,
				err,
			)
		}
		sim.logger.Debug("Verilator RunTest: Successfully copied %s to %s", srcPath, outputPath)
	}

	sim.logger.Debug("Verilator RunTest completed successfully.")
	return nil
}
