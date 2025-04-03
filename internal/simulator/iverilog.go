package simulator

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"time"

	"github.com/jns/pfuzz/pkg/utils"
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
		execPath: filepath.Join(workDir, "ibex_sim_iv"),
		workDir:  workDir,
		debug:    utils.NewDebugLogger(verbose),
	}
}

// Compile compiles the verilog files with IVerilog
func (sim *IVerilogSimulator) Compile() error {
	sim.debug.Printf("DEBUG: Starting IVerilog compile in %s", sim.workDir)

	// Look for the Verilog file directly in the work directory first
	verilogPath := filepath.Join(sim.workDir, "ibex_branch_predict_mocked.sv")
	testbenchPath := filepath.Join(sim.workDir, "testbench.sv")

	// First verify that the source files exist or copy them
	if _, err := os.Stat(verilogPath); os.IsNotExist(err) {
		sim.debug.Printf("DEBUG: Source verilog file not found at %s, copying from TMP_DIR", verilogPath)
		// Copy from TMP_DIR
		tmpVerilogPath := filepath.Join(utils.TMP_DIR, "ibex_branch_predict_mocked.sv")
		if _, err := os.Stat(tmpVerilogPath); os.IsNotExist(err) {
			return fmt.Errorf("verilog file not found at source: %s", tmpVerilogPath)
		}

		// Make sure the directory exists
		if err := os.MkdirAll(filepath.Dir(verilogPath), 0755); err != nil {
			return fmt.Errorf("failed to create directory for verilog file: %v", err)
		}

		if err := utils.CopyFile(tmpVerilogPath, verilogPath); err != nil {
			return fmt.Errorf("failed to copy verilog file to work dir: %v", err)
		}
		sim.debug.Printf("DEBUG: Copied verilog file from %s to %s", tmpVerilogPath, verilogPath)
	}

	if _, err := os.Stat(testbenchPath); os.IsNotExist(err) {
		sim.debug.Printf("DEBUG: Source testbench file not found at %s, copying from TMP_DIR", testbenchPath)
		// Copy from TMP_DIR
		tmpTestbenchPath := filepath.Join(utils.TMP_DIR, "testbench.sv")
		if _, err := os.Stat(tmpTestbenchPath); os.IsNotExist(err) {
			return fmt.Errorf("testbench file not found at source: %s", tmpTestbenchPath)
		}

		if err := utils.CopyFile(tmpTestbenchPath, testbenchPath); err != nil {
			return fmt.Errorf("failed to copy testbench to work dir: %v", err)
		}
		sim.debug.Printf("DEBUG: Copied testbench file from %s to %s", tmpTestbenchPath, testbenchPath)
	}

	// Verify files exist in work directory
	if _, err := os.Stat(verilogPath); os.IsNotExist(err) {
		return fmt.Errorf("verilog file not found at: %s", verilogPath)
	}

	if _, err := os.Stat(testbenchPath); os.IsNotExist(err) {
		return fmt.Errorf("testbench file not found at: %s", testbenchPath)
	}

	// Create output directory
	outDir := filepath.Dir(sim.execPath)
	if err := os.MkdirAll(outDir, 0755); err != nil {
		return fmt.Errorf("failed to create output directory: %v", err)
	}
	sim.debug.Printf("DEBUG: Ensured output directory exists: %s", outDir)

	// Compile directly in the work directory with simple command
	cmdArgs := []string{"-o", "ibex_sim_iv", "ibex_branch_predict_mocked.sv", "testbench.sv", "-g2012"}
	sim.debug.Printf("DEBUG: Running iverilog command: iverilog %s in directory %s", strings.Join(cmdArgs, " "), sim.workDir)

	cmd := exec.Command("iverilog", cmdArgs...)
	cmd.Dir = sim.workDir
	var stderr bytes.Buffer
	var stdout bytes.Buffer
	cmd.Stderr = &stderr
	cmd.Stdout = &stdout

	if err := cmd.Run(); err != nil {
		sim.debug.Printf("DEBUG: iverilog command failed: %v", err)
		sim.debug.Printf("DEBUG: stderr: %s", stderr.String())
		return fmt.Errorf("iverilog compilation failed: %v - %s", err, stderr.String())
	}
	if stdout.Len() > 0 {
		sim.debug.Printf("DEBUG: iverilog stdout: %s", stdout.String())
	}

	// Check if executable was created
	execPath := filepath.Join(sim.workDir, "ibex_sim_iv")
	sim.debug.Printf("DEBUG: Checking for compiled executable at %s", execPath)
	fileInfo, err := os.Stat(execPath)
	if err != nil {
		if os.IsNotExist(err) {
			// List the directory contents to debug
			files, _ := os.ReadDir(sim.workDir)
			fileNames := make([]string, 0, len(files))
			for _, f := range files {
				fileNames = append(fileNames, f.Name())
			}
			sim.debug.Printf("DEBUG: Directory contents: %v", fileNames)
			return fmt.Errorf("executable not created at: %s (directory exists: %v)", execPath, true)
		}
		return fmt.Errorf("error checking executable: %v", err)
	}
	sim.debug.Printf("DEBUG: Found executable, size: %d bytes, mode: %s", fileInfo.Size(), fileInfo.Mode())

	// Make sure the executable has the right permissions
	if err := os.Chmod(execPath, 0755); err != nil {
		return fmt.Errorf("failed to set executable permissions: %v", err)
	}
	sim.debug.Printf("DEBUG: Set executable permissions to 0755")

	// Verify executable exists and has non-zero size
	if fileInfo.Size() == 0 {
		return fmt.Errorf("executable has zero size at: %s", execPath)
	}

	// Run a quick test run of the executable to verify it's a valid binary
	sim.debug.Printf("DEBUG: Testing executable with 'file' command")
	fileCmd := exec.Command("file", execPath)
	var fileOutput bytes.Buffer
	fileCmd.Stdout = &fileOutput
	if err := fileCmd.Run(); err == nil {
		sim.debug.Printf("DEBUG: file command output: %s", fileOutput.String())
	}

	return nil
}

// RunTest runs the simulator with specific input and output files
func (sim *IVerilogSimulator) RunTest(inputPath, pcPath, validPath, takenPath, targetPath string) error {
	// Use worker-specific temporary files - store them directly in the work dir
	tmpInputPath := filepath.Join(sim.workDir, "input.hex")
	tmpPcPath := filepath.Join(sim.workDir, "pc.hex")
	tmpValidPath := filepath.Join(sim.workDir, "valid.hex")
	tmpTakenPath := filepath.Join(sim.workDir, "taken.hex")
	tmpTargetPath := filepath.Join(sim.workDir, "target.hex")

	// Make sure any existing output files are removed first
	os.Remove(tmpTakenPath)
	os.Remove(tmpTargetPath)
	sim.debug.Printf("DEBUG: Cleared any existing output files")

	// Copy input files (simple, synchronous approach)
	if err := utils.CopyFile(inputPath, tmpInputPath); err != nil {
		return fmt.Errorf("failed to copy input file: %v", err)
	}
	if err := utils.CopyFile(pcPath, tmpPcPath); err != nil {
		return fmt.Errorf("failed to copy PC file: %v", err)
	}
	if err := utils.CopyFile(validPath, tmpValidPath); err != nil {
		return fmt.Errorf("failed to copy valid file: %v", err)
	}
	sim.debug.Printf("DEBUG: Copied input files successfully")

	// Verify that the executable exists
	if _, err := os.Stat(sim.execPath); os.IsNotExist(err) {
		return fmt.Errorf("iverilog executable not found at: %s", sim.execPath)
	}

	relExecPath := filepath.Base(sim.execPath)
	cmd := exec.Command("vvp", relExecPath)

	cmd.Dir = sim.workDir
	var stderr bytes.Buffer
	var stdout bytes.Buffer
	cmd.Stderr = &stderr
	cmd.Stdout = &stdout

	if err := cmd.Run(); err != nil {
		sim.debug.Printf("DEBUG: vvp execution failed with error: %v", err)
		sim.debug.Printf("DEBUG: stderr: %s", stderr.String())
		sim.debug.Printf("DEBUG: stdout: %s", stdout.String())
		return fmt.Errorf("iverilog execution failed: %v - %s", err, stderr.String())
	}

	sim.debug.Printf("DEBUG: Simulation completed successfully")

	// Wait to ensure file system has completed writing the files
	time.Sleep(100 * time.Millisecond)

	// Verify files exist with multiple retries
	if err := VerifyOutputFiles(tmpTakenPath, tmpTargetPath); err != nil {
		return err
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

// GetExecPath returns the path to the compiled simulator executable
func (sim *IVerilogSimulator) GetExecPath() string {
	return sim.execPath
}
