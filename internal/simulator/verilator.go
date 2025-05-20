package simulator

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"time"

	"github.com/toby-bro/pfuzz/internal/verilog"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

// VerilatorSimulator represents the Verilator simulator
type VerilatorSimulator struct {
	execPath  string
	workDir   string
	svFile    *verilog.VerilogFile
	module    *verilog.Module
	optimized bool
	logger    *utils.DebugLogger
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
		panic(fmt.Sprintf("Module %s not found in Verilog file", moduleName))
	}
	return &VerilatorSimulator{
		execPath:  filepath.Join(workDir, "obj_dir", "Vtestbench"),
		workDir:   workDir,
		svFile:    svFile,
		module:    svFile.Modules[moduleName],
		optimized: optimized,
		logger:    utils.NewDebugLogger(verbose),
	}
}

// Compile compiles the verilog files with Verilator
func (sim *VerilatorSimulator) Compile() error {
	// Create the obj_dir in the worker directory
	objDir := filepath.Join(sim.workDir, "obj_dir")
	if err := os.MkdirAll(objDir, 0o755); err != nil {
		return fmt.Errorf("failed to create obj_dir: %v", err)
	}

	testbenchPath := filepath.Join(filepath.Dir(sim.workDir), "testbench.sv")

	// Verify the testbench file exists and has content
	if info, err := os.Stat(testbenchPath); err != nil || info.Size() == 0 {
		return fmt.Errorf("testbench.sv is missing or empty in %s", filepath.Dir(sim.workDir))
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
		"-Wno-UNDRIVEN",
		"-Wno-UNOPTFLAT",
		"-Wno-UNUSED",
		"-Wno-UNSIGNED",
		"-Wno-WIDTHEXPAND",
		"-Wno-WIDTHTRUNC",
		"-Wno-MULTITOP",
		"-Wno-CASEINCOMPLETE",
		"-Wno-CASEOVERLAP",
		"../testbench.sv",
	}

	if sim.optimized {
		verilatorArgs = append(verilatorArgs, "-O3")
	} else {
		verilatorArgs = append(verilatorArgs, "-O0")
	}

	// Run Verilator in the worker directory
	cmd := exec.Command("verilator", verilatorArgs...)
	cmd.Dir = sim.workDir

	var stderr bytes.Buffer
	cmd.Stderr = &stderr

	/* sim.logger.Debug(
	 *	"Verilator command details: Path=%s, Dir=%s, Args=%v",
	 *	cmd.Path,
	 *	cmd.Dir,
	 *	cmd.Args,
	 *)
	 *sim.logger.Debug("Verilator command: %s", cmd.String())
	 */

	err := cmd.Run()
	if err != nil {
		// retry
		sim.logger.Warn("[%s] Verilator compilation failed, retrying...", sim.workDir)
		time.Sleep(10 * time.Millisecond)
		err = cmd.Run()
		if err != nil {
			return fmt.Errorf(
				"[%s] verilator compilation failed: %v\n%s",
				sim.workDir,
				err,
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

// RunTest runs the simulator with provided input directory and output paths
func (sim *VerilatorSimulator) RunTest(inputDir string, outputPaths map[string]string) error {
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

	// 4. Run the simulation executable
	// Execute the binary relative to the working directory.
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

	if err := cmd.Run(); err != nil {
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
	for portName, outputPath := range outputPaths {
		srcPath := filepath.Join(sim.workDir, fmt.Sprintf("output_%s.hex", portName))
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
				portName,
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
				portName,
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
