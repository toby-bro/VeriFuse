package fuzz

import (
	"bytes"
	"fmt"
	"log"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"time"

	"github.com/toby-bro/pfuzz/internal/mocker"
	"github.com/toby-bro/pfuzz/internal/simulator"
	"github.com/toby-bro/pfuzz/internal/testgen"
	"github.com/toby-bro/pfuzz/internal/verilog"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

// Test file prefixes for different simulators
const (
	IV_PREFIX = "iv_"
	VL_PREFIX = "vl_"
)

// Fuzzer is the main fuzzing orchestrator
type Fuzzer struct {
	stats       *Stats
	strategy    Strategy
	workers     int
	verbose     bool
	seed        int64
	debug       *utils.DebugLogger
	verilogFile string
	moduleName  string
	module      *verilog.Module
}

// NewFuzzer creates a new fuzzer instance
func NewFuzzer(
	strategy string,
	workers int,
	verbose bool,
	seed int64,
	verilogFile string,
	moduleName string,
) *Fuzzer {
	var s Strategy

	fuzzer := &Fuzzer{
		stats:       NewStats(),
		workers:     workers,
		verbose:     verbose,
		seed:        seed,
		debug:       utils.NewDebugLogger(verbose),
		verilogFile: verilogFile,
		moduleName:  moduleName,
	}

	// Create strategy after module parsing so it knows input/output structure
	switch strategy {
	case "simple":
		s = &SimpleStrategy{seed: seed}
	case "smart":
		s = &SmartStrategy{seed: seed}
	default:
		s = &RandomStrategy{seed: seed}
	}

	fuzzer.strategy = s
	return fuzzer
}

// PrepareSVFile analyzes and prepares the Verilog file for testing
func PrepareSVFile(initialVerilogFile string, mockedVerilogPath string, mock bool) error {
	// Analyze and mock Verilog file
	if mock {
		content, err := mocker.MockVerilogFile(initialVerilogFile)
		if err != nil {
			return fmt.Errorf("failed to analyze Verilog file: %v", err)
		}

		// Create the mocked verilog file
		if err := utils.WriteFileContent(mockedVerilogPath, content); err != nil {
			return fmt.Errorf("failed to write mocked SV file: %v", err)
		}
		log.Printf("Created mocked SystemVerilog file: %s", mockedVerilogPath)
	} else {
		// Copy the original file to the mocked path
		if err := utils.CopyFile(initialVerilogFile, mockedVerilogPath); err != nil {
			return fmt.Errorf("failed to copy original Verilog file: %v", err)
		}
	}

	// Verify the file exists
	if _, err := os.Stat(mockedVerilogPath); os.IsNotExist(err) {
		return fmt.Errorf("mocked verilog file was not created at %s", mockedVerilogPath)
	}
	return nil
}

func addMockedSuffix(filename string) string {
	ext := filepath.Ext(filename)
	base := strings.TrimSuffix(filename, ext)
	newFilename := base + "_mocked" + ext
	return newFilename
}

// Setup prepares the environment for fuzzing
func (f *Fuzzer) Setup(mock bool) error {
	// Ensure directories exist first
	if err := utils.EnsureDirs(); err != nil {
		return fmt.Errorf("failed to create directories: %v", err)
	}

	// Parse the Verilog file to extract module information
	module, err := verilog.ParseVerilogFile(f.verilogFile, f.moduleName)
	if err != nil {
		return fmt.Errorf("failed to parse Verilog file: %v", err)
	}
	f.module = module

	if mock {
		f.module.Name = addMockedSuffix(module.Name)
		f.verilogFile = addMockedSuffix(f.verilogFile)
	}

	// Update the strategy with module information
	if moduleAwareStrategy, ok := f.strategy.(ModuleAwareStrategy); ok {
		moduleAwareStrategy.SetModule(module)
	}

	f.debug.Log("Parsed module '%s' with %d ports", module.Name, len(module.Ports))

	for i, port := range module.Ports {
		dirStr := "INPUT"
		switch port.Direction {
		case verilog.OUTPUT:
			dirStr = "OUTPUT"
		case verilog.INOUT:
			dirStr = "INOUT"
		case verilog.INPUT:
			dirStr = "INPUT"
		}
		f.debug.Log("  Port %d: %s (%s) [%d bits]", i+1, port.Name, dirStr, port.Width)
	}

	// Prepare mocked Verilog file
	VerilogFileName := filepath.Base(f.verilogFile)
	VerilogPath := filepath.Join(utils.TMP_DIR, VerilogFileName)

	if err := PrepareSVFile(f.verilogFile, VerilogPath, mock); err != nil {
		return err
	}

	// Generate testbenches based on module information
	gen := testgen.NewGenerator(module)
	if err := gen.GenerateTestbenches(); err != nil {
		return fmt.Errorf("failed to generate testbenches: %v", err)
	}

	testbenchPath := filepath.Join(utils.TMP_DIR, "testbench.sv")
	if _, err := os.Stat(testbenchPath); os.IsNotExist(err) {
		return fmt.Errorf("testbench file was not created at %s", testbenchPath)
	}

	f.debug.Log("Created testbenches in %s directory", utils.TMP_DIR)

	// Create a setup directory for compilation
	setupDir := filepath.Join(utils.TMP_DIR, "setup")
	if err := os.MkdirAll(setupDir, 0o755); err != nil {
		return fmt.Errorf("failed to create setup directory: %v", err)
	}

	// Copy the necessary files to the setup directory
	setupVerilogPath := filepath.Join(setupDir, VerilogFileName)
	setupTestbenchPath := filepath.Join(setupDir, "testbench.sv")

	if err := utils.CopyFile(VerilogPath, setupVerilogPath); err != nil {
		return fmt.Errorf("failed to copy Verilog file to setup dir: %v", err)
	}

	if err := utils.CopyFile(testbenchPath, setupTestbenchPath); err != nil {
		return fmt.Errorf("failed to copy testbench to setup dir: %v", err)
	}

	// Verify the copied files exist in the setup directory
	if _, err := os.Stat(setupVerilogPath); os.IsNotExist(err) {
		return fmt.Errorf("failed to verify copied verilog file in setup dir: %s", setupVerilogPath)
	}

	if _, err := os.Stat(setupTestbenchPath); os.IsNotExist(err) {
		return fmt.Errorf("failed to verify copied testbench in setup dir: %s", setupTestbenchPath)
	}

	// Test IVerilog and Verilator compilation
	if err := testIVerilog(setupDir); err != nil {
		return fmt.Errorf("iverilog test failed: %v", err)
	}
	if err := testVerilator(setupDir, module.Name); err != nil {
		return fmt.Errorf("verilator test failed: %v", err)
	}

	return nil
}

func testIVerilog(setupDir string) error {
	// Test basic IVerilog functionality
	testFile := filepath.Join(setupDir, "test.sv")
	testContent := `
    module test;
      initial begin
        $display("IVerilog test");
        $finish;
      end
    endmodule
    `
	if err := os.WriteFile(testFile, []byte(testContent), 0o644); err != nil {
		return fmt.Errorf("failed to write IVerilog test file: %v", err)
	}

	// Test IVerilog with a simple compilation first
	testExecPath := "test"
	cmd := exec.Command("iverilog", "-o", testExecPath, "test.sv")
	cmd.Dir = setupDir
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	if err := cmd.Run(); err != nil {
		return fmt.Errorf(
			"iverilog basic test failed, check your installation: %v - %s",
			err,
			stderr.String(),
		)
	}

	// Now compile actual module
	log.Println("Compiling iverilog in setup directory...")
	ivCmd := exec.Command("iverilog", "-o", "module_sim_iv",
		"testbench.sv", "-g2012", "-gsupported-assertions")
	ivCmd.Dir = setupDir
	stderr.Reset()
	ivCmd.Stderr = &stderr
	if err := ivCmd.Run(); err != nil {
		return fmt.Errorf("iverilog compilation failed: %v - %s", err, stderr.String())
	}

	// Verify iverilog executable was created
	ivExecPath := filepath.Join(setupDir, "module_sim_iv")
	if _, err := os.Stat(ivExecPath); os.IsNotExist(err) {
		return fmt.Errorf("iverilog executable not created at %s", ivExecPath)
	}

	log.Println("Successfully compiled with iverilog")
	return nil
}

func testVerilator(setupDir string, moduleName string) error {
	// For verilator, use the simulator with proper error handling
	vlsim := simulator.NewVerilatorSimulator(setupDir, moduleName)
	if err := vlsim.Compile(); err != nil {
		return fmt.Errorf("failed to compile with verilator: %v", err)
	}
	log.Println("Successfully compiled with verilator")
	return nil
}

// Run performs the fuzzing
func (f *Fuzzer) Run(numTests int) error {
	f.debug.Log("Starting fuzzing with %d test cases using strategy: %s\n",
		numTests, f.strategy.Name())
	f.debug.Log("Target module: %s with %d ports", f.module.Name, len(f.module.Ports))

	// Count inputs and outputs
	inputCount := 0
	outputCount := 0
	for _, port := range f.module.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			inputCount++
		}
		if port.Direction == verilog.OUTPUT {
			outputCount++
		}
	}
	f.debug.Log("Module has %d inputs and %d outputs", inputCount, outputCount)

	// Create a worker pool for parallel fuzzing
	var wg sync.WaitGroup
	testCases := make(chan int, f.workers)

	// Progress tracking
	progressTracker := NewProgressTracker(numTests, f.stats)
	progressTracker.Start()
	defer progressTracker.Stop()

	// Start worker goroutines
	for w := 0; w < f.workers; w++ {
		wg.Add(1)
		go f.worker(&wg, testCases)
	}

	// Feed test cases to workers
	for i := 0; i < numTests; i++ {
		testCases <- i
	}
	close(testCases)

	// Wait for all workers to finish
	wg.Wait()

	// Print summary
	f.stats.PrintSummary()

	if f.stats.Mismatches > 0 {
		f.debug.Log("Found %d mismatches between iverilog and verilator!\n", f.stats.Mismatches)
		return fmt.Errorf("%d mismatches found", f.stats.Mismatches)
	}

	f.debug.Log("No mismatches found after %d tests.\n", numTests)
	return nil
}

// compareOutputValues compares output values from different simulators with special handling for xx/00
func compareOutputValues(ivValue, vlValue string) bool {
	// Clean and normalize the values
	ivNorm := strings.TrimSpace(strings.ToLower(ivValue))
	vlNorm := strings.TrimSpace(strings.ToLower(vlValue))

	// Direct match case
	if ivNorm == vlNorm {
		return true
	}

	// Special handling: Consider "xx" from Verilator equivalent to "00" from IVerilog
	// Both represent "nothing triggered" states
	if (ivNorm == "00" && vlNorm == "xx") || (ivNorm == "xx" && vlNorm == "00") {
		return true
	}

	// Consider "x" equivalent to "0" for single bit values
	if (ivNorm == "0" && vlNorm == "x") || (ivNorm == "x" && vlNorm == "0") {
		return true
	}

	// If one output has "x" bits and the other has "0"s in the same positions,
	// they may represent the same uninitialized or don't-care state
	if len(ivNorm) == len(vlNorm) && ivNorm != vlNorm {
		// Only check if one contains 'x' characters
		if strings.Contains(ivNorm, "x") || strings.Contains(vlNorm, "x") {
			equivalent := true
			for i := 0; i < len(ivNorm); i++ {
				// Check if character at this position is either the same in both outputs,
				// or is an 'x' in one output and '0' in the other
				charMatch := ivNorm[i] == vlNorm[i] ||
					(ivNorm[i] == 'x' && vlNorm[i] == '0') ||
					(ivNorm[i] == '0' && vlNorm[i] == 'x')

				if !charMatch {
					equivalent = false
					break
				}
			}
			return equivalent
		}
	}

	// Not equivalent
	return false
}

// setupWorker creates the worker directory and sets up deferred cleanup.
func (f *Fuzzer) setupWorker(workerID string) (string, func(), error) {
	workerDir := filepath.Join(utils.TMP_DIR, workerID)
	f.debug.Printf("[%s]: Creating worker directory at %s", workerID, workerDir)

	if err := os.MkdirAll(workerDir, 0o755); err != nil {
		return "", nil, fmt.Errorf("failed to create worker directory %s: %w", workerDir, err)
	}

	cleanup := func() {
		if err := os.RemoveAll(workerDir); err != nil {
			log.Printf("Warning: Failed to clean up worker directory %s: %v", workerDir, err)
		} else if f.verbose {
			log.Printf("Cleaned up worker directory: %s", workerDir)
		}
	}

	return workerDir, cleanup, nil
}

// copyWorkerFiles copies necessary source files to the worker directory.
func (f *Fuzzer) copyWorkerFiles(workerID, workerDir, verilogFileName string) error {
	f.debug.Printf("[%s]: Copying source files to worker directory", workerID)
	setupFiles := []string{
		verilogFileName,
		"testbench.sv",
		"testbench.cpp", // IMPORTANT: Make sure to include testbench.cpp
	}

	for _, filename := range setupFiles {
		srcPath := filepath.Join(utils.TMP_DIR, filename)
		dstPath := filepath.Join(workerDir, filename)

		// Skip if source doesn't exist, but log it
		if _, err := os.Stat(srcPath); os.IsNotExist(err) {
			f.debug.Printf(
				"[%s]: Warning: Source file %s does not exist, skipping",
				workerID,
				srcPath,
			)
			continue
		}

		if err := utils.CopyFile(srcPath, dstPath); err != nil {
			return fmt.Errorf("failed to copy %s to worker directory: %w", filename, err)
		}

		// Verify the file was copied successfully
		if fi, err := os.Stat(dstPath); err != nil || fi.Size() == 0 {
			fileSize := int64(0)
			if fi != nil {
				fileSize = fi.Size()
			}
			return fmt.Errorf("[%s]: File %s not copied correctly, size: %d, error: %v",
				workerID, dstPath, fileSize, err)
		}
		f.debug.Printf("[%s]: Successfully copied %s", workerID, filename)
	}
	return nil
}

// setupSimulators creates and compiles simulators for the worker.
func (f *Fuzzer) setupSimulators(
	workerID, workerDir string,
) (simulator.Simulator, simulator.Simulator, error) {
	f.debug.Printf("[%s]: Creating simulators", workerID)
	ivsim := simulator.NewIVerilogSimulator(workerDir, f.verbose)
	vlsim := simulator.NewVerilatorSimulator(workerDir, f.module.Name)

	// Compile simulators
	f.debug.Printf("[%s]: Compiling IVerilog simulator", workerID)
	if err := ivsim.Compile(); err != nil {
		return nil, nil, fmt.Errorf("failed to compile IVerilog in worker %s: %w", workerID, err)
	}

	f.debug.Printf("[%s]: Compiling Verilator simulator", workerID)
	if err := vlsim.Compile(); err != nil {
		return nil, nil, fmt.Errorf("failed to compile Verilator in worker %s: %w", workerID, err)
	}

	return ivsim, vlsim, nil
}

// processTestCases processes individual test cases received from the channel.
func (f *Fuzzer) processTestCases(
	workerID, workerDir string,
	ivsim, vlsim simulator.Simulator,
	testCases <-chan int,
) {
	for i := range testCases {
		f.runSingleTest(workerID, workerDir, ivsim, vlsim, i)
	}
}

// runSingleTest executes a single fuzzing test case.
func (f *Fuzzer) runSingleTest(
	workerID, workerDir string,
	ivsim, vlsim simulator.Simulator,
	testIndex int,
) {
	testCase := f.strategy.GenerateTestCase(testIndex)
	f.stats.AddTest()

	// Add validation for multi-bit signals (optional, kept for consistency)
	f.validateMultiBitSignals(testCase)

	// Create test directory within worker directory
	testDir := filepath.Join(workerDir, fmt.Sprintf("test_%d", testIndex))
	if err := os.MkdirAll(testDir, 0o755); err != nil {
		log.Printf("[%s] Failed to create test directory %s: %v", workerID, testDir, err)
		f.stats.AddSimError()
		return
	}
	defer func() {
		// Explicitly clean up test files after each test unless verbose
		if !f.verbose {
			os.RemoveAll(testDir)
		}
	}()

	// Write input files
	if err := writeTestInputs(testDir, testCase); err != nil {
		log.Printf("[%s] Failed to write inputs for test %d: %v", workerID, testIndex, err)
		f.stats.AddSimError()
		return
	}

	// Run both simulators
	ivResult, ivSuccess := f.runSimulator("iverilog", ivsim, testDir)
	if !ivSuccess {
		log.Printf("[%s] IVerilog simulation failed for test %d", workerID, testIndex)
		// No need to add sim error here, runSimulator already did
		return
	}

	vlResult, vlSuccess := f.runSimulator("verilator", vlsim, testDir)
	if !vlSuccess {
		log.Printf("[%s] Verilator simulation failed for test %d", workerID, testIndex)
		// No need to add sim error here, runSimulator already did
		return
	}

	// Compare results
	mismatch, mismatchDetails := f.compareSimulationResults(ivResult, vlResult)

	if mismatch {
		f.handleMismatch(testIndex, testDir, testCase, mismatchDetails, ivResult)
	}
}

// validateMultiBitSignals checks if multi-bit input values seem reasonable.
func (f *Fuzzer) validateMultiBitSignals(testCase map[string]string) {
	for _, port := range f.module.Ports {
		if port.Width > 1 {
			value, exists := testCase[port.Name]
			if exists {
				// Check if the value is likely a hex string of proper width
				expectedLen := (port.Width + 3) / 4 // Number of expected hex digits
				// Allow exact length or length+1 if it starts with 0x/0b? For now, just check minimum.
				// A single hex digit represents up to 4 bits.
				if len(value) > 0 && len(value) < expectedLen {
					f.debug.Printf(
						"Warning: Port %s (width %d) has value '%s' which might be shorter than expected (%d hex digits)",
						port.Name,
						port.Width,
						value,
						expectedLen,
					)
				}
			}
		}
	}
}

// compareSimulationResults compares the outputs from two simulators.
func (f *Fuzzer) compareSimulationResults(
	ivResult, vlResult map[string]string,
) (bool, map[string]string) {
	mismatch := false
	mismatchDetails := make(map[string]string)

	for portName, ivValue := range ivResult {
		if vlValue, exists := vlResult[portName]; exists {
			if !compareOutputValues(ivValue, vlValue) {
				mismatch = true
				mismatchDetails[portName] = fmt.Sprintf(
					"IVerilog=%s, Verilator=%s",
					ivValue,
					vlValue,
				)
			}
		} else {
			// Handle case where one simulator produced output but the other didn't
			// This might indicate an error or a difference in how outputs are handled
			// For now, log it as a potential issue, but might not be a 'mismatch' per se
			// depending on requirements. Let's consider it a mismatch for now.
			mismatch = true
			mismatchDetails[portName] = fmt.Sprintf(
				"IVerilog=%s, Verilator=MISSING",
				ivValue,
			)
			f.debug.Printf("Warning: Output for port %s missing from Verilator result", portName)
		}
	}

	// Check for outputs present in Verilator but not IVerilog
	for portName, vlValue := range vlResult {
		if _, exists := ivResult[portName]; !exists {
			mismatch = true
			mismatchDetails[portName] = "IVerilog=MISSING, Verilator=" + vlValue
			f.debug.Printf("Warning: Output for port %s missing from IVerilog result", portName)
		}
	}

	return mismatch, mismatchDetails
}

// handleMismatch logs the mismatch details and saves the relevant files.
func (f *Fuzzer) handleMismatch(
	testIndex int,
	testDir string,
	testCase map[string]string,
	mismatchDetails map[string]string,
	ivResult map[string]string,
) {
	log.Printf("Mismatch found in test %d:\n", testIndex)

	// Display input values
	log.Printf("Inputs:\n")
	for portName, value := range testCase {
		log.Printf("  %s = %s\n", portName, value)
	}

	// Display mismatched outputs
	log.Printf("Mismatched outputs:\n")
	for portName, detail := range mismatchDetails {
		log.Printf("  %s: %s\n", portName, detail)
	}

	// Save the complete test case files for replay
	mismatchDir := filepath.Join(utils.MISMATCHES_DIR, fmt.Sprintf("mismatch_%d", testIndex))
	if err := os.MkdirAll(mismatchDir, 0o755); err != nil {
		log.Printf("Failed to create mismatch directory %s: %v", mismatchDir, err)
		// Continue processing stats even if saving fails
	} else {
		// Copy input files
		for portName := range testCase {
			inputFile := fmt.Sprintf("input_%s.hex", portName)
			src := filepath.Join(testDir, inputFile)
			dst := filepath.Join(mismatchDir, inputFile)
			if err := utils.CopyFile(src, dst); err != nil {
				log.Printf("Failed to copy input file %s: %v", inputFile, err)
			}
		}

		// Copy output files from both simulators
		// Determine output ports from ivResult keys (assuming ivResult is complete if successful)
		// or potentially from f.module.Ports if needed
		outputPorts := make(map[string]struct{})
		for portName := range ivResult { // Assuming ivResult contains all expected output ports
			outputPorts[portName] = struct{}{}
		}
		// Add any ports from mismatchDetails that might have been missing in one result
		for portName := range mismatchDetails {
			outputPorts[portName] = struct{}{}
		}

		for portName := range outputPorts {
			ivFile := filepath.Join(testDir, fmt.Sprintf("%s%s.hex", IV_PREFIX, portName))
			vlFile := filepath.Join(testDir, fmt.Sprintf("%s%s.hex", VL_PREFIX, portName))

			if utils.FileExists(ivFile) {
				dst := filepath.Join(mismatchDir, fmt.Sprintf("%s%s.hex", IV_PREFIX, portName))
				if err := utils.CopyFile(ivFile, dst); err != nil {
					log.Printf("Failed to copy IVerilog output file %s: %v", ivFile, err)
				}
			}

			if utils.FileExists(vlFile) {
				dst := filepath.Join(mismatchDir, fmt.Sprintf("%s%s.hex", VL_PREFIX, portName))
				if err := utils.CopyFile(vlFile, dst); err != nil {
					log.Printf("Failed to copy Verilator output file %s: %v", vlFile, err)
				}
			}
		}

		// Create a summary file
		summaryPath := filepath.Join(mismatchDir, fmt.Sprintf("mismatch_%d_summary.txt", testIndex))
		file, err := os.Create(summaryPath)
		if err == nil {
			defer file.Close()
			fmt.Fprintf(file, "Test case %d\n\n", testIndex)
			fmt.Fprintf(file, "Inputs:\n")
			for portName, value := range testCase {
				fmt.Fprintf(file, "  %s = %s\n", portName, value)
			}
			fmt.Fprintf(file, "\nMismatched outputs:\n")
			for portName, detail := range mismatchDetails {
				fmt.Fprintf(file, "  %s: %s\n", portName, detail)
			}
		} else {
			log.Printf("Failed to create mismatch summary file %s: %v", summaryPath, err)
		}
	}

	f.stats.AddMismatch(testCase)
}

// worker is a goroutine that processes test cases
func (f *Fuzzer) worker(wg *sync.WaitGroup, testCases <-chan int) {
	defer wg.Done()

	VerilogFileName := filepath.Base(f.verilogFile)
	workerID := fmt.Sprintf("worker_%d_%d", os.Getpid(), time.Now().UnixNano()) // More unique ID

	// Setup worker directory and cleanup
	workerDir, cleanup, err := f.setupWorker(workerID)
	if err != nil {
		log.Printf("Worker setup failed for %s: %v", workerID, err)
		// Cannot proceed without worker directory
		return
	}
	defer cleanup() // Ensure cleanup runs when worker exits

	// Copy necessary files
	if err := f.copyWorkerFiles(workerID, workerDir, VerilogFileName); err != nil {
		log.Printf("Failed to copy files for worker %s: %v", workerID, err)
		return // Cannot proceed without source files
	}

	// Setup simulators
	ivsim, vlsim, err := f.setupSimulators(workerID, workerDir)
	if err != nil {
		log.Printf("Simulator setup failed for worker %s: %v", workerID, err)
		// Cannot proceed without simulators
		return
	}

	// Process test cases using a separate function
	f.processTestCases(workerID, workerDir, ivsim, vlsim, testCases)
}

// writeTestInputs writes test case input files
func writeTestInputs(testDir string, testCase map[string]string) error {
	// Write all input files
	for portName, value := range testCase {
		inputPath := filepath.Join(testDir, fmt.Sprintf("input_%s.hex", portName))
		if err := os.WriteFile(inputPath, []byte(value), 0o644); err != nil {
			return fmt.Errorf("failed to write input file %s: %v", inputPath, err)
		}
	}
	return nil
}

// runSimulator executes a simulator and collects output results
func (f *Fuzzer) runSimulator(
	simName string,
	sim simulator.Simulator,
	testDir string,
) (map[string]string, bool) {
	outputDir := filepath.Join(testDir, simName)
	if err := os.MkdirAll(outputDir, 0o755); err != nil {
		f.stats.AddSimError()
		return nil, false
	}

	// Prepare output file paths - ensure consistent naming convention
	outputPaths := make(map[string]string)
	for _, port := range f.module.Ports {
		if port.Direction == verilog.OUTPUT {
			var prefix string
			if simName == "iverilog" {
				prefix = IV_PREFIX // "iv_"
			} else {
				prefix = VL_PREFIX // "vl_" - was previously using simName[:2] which gave "ve_" for verilator
			}
			outputFile := fmt.Sprintf("%s%s.hex", prefix, port.Name)
			outputPaths[port.Name] = filepath.Join(testDir, outputFile)
		}
	}

	// Run the simulator
	if err := sim.RunTest(testDir, outputPaths); err != nil {
		f.stats.AddSimError()
		return nil, false
	}

	// Verify all output files were created
	if err := simulator.VerifyOutputFiles(outputPaths); err != nil {
		f.stats.AddSimError()
		return nil, false
	}

	// Read all output values using the utility function
	results, err := simulator.ReadOutputFiles(outputPaths)
	if err != nil {
		f.stats.AddSimError()
		return nil, false
	}

	return results, true
}
