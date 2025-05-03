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

	// Parse the *original* Verilog file to extract module information for reference
	// The actual module used by workers might be mutated.
	originalModule, err := verilog.ParseVerilogFile(f.verilogFile, f.moduleName)
	if err != nil {
		return fmt.Errorf("failed to parse original Verilog file: %v", err)
	}
	f.module = originalModule // Store the original module info

	originalVerilogFile := f.verilogFile // Keep track of the original path
	originalModuleName := f.moduleName

	if mock {
		// If mocking, update the expected module name and file path for the mocked version
		f.module.Name = addMockedSuffix(originalModule.Name)
		f.verilogFile = addMockedSuffix(f.verilogFile)
		f.moduleName = f.module.Name // Update moduleName to the mocked one
	}

	// Update the strategy with *original* module information
	if moduleAwareStrategy, ok := f.strategy.(ModuleAwareStrategy); ok {
		moduleAwareStrategy.SetModule(f.module) // Strategy uses original module structure
	}

	f.debug.Log("Parsed original module '%s' with %d ports", f.module.Name, len(f.module.Ports))

	// Prepare the Verilog file (mocked or copied) in the main tmp directory
	// Workers will copy this file and potentially mutate it.
	verilogFileName := filepath.Base(f.verilogFile)
	verilogPath := filepath.Join(utils.TMP_DIR, verilogFileName)

	// Use the original file path for PrepareSVFile if mocking, otherwise use the (potentially already suffixed) f.verilogFile
	sourceFileForPrepare := originalVerilogFile
	if !mock {
		sourceFileForPrepare = f.verilogFile
	}

	if err := PrepareSVFile(sourceFileForPrepare, verilogPath, mock); err != nil {
		return err
	}

	// Testbench generation and compilation are moved to workers.
	// Just test the availability of the simulation tools here.
	f.debug.Log("Verilog file prepared at %s", verilogPath)

	// Test IVerilog and Verilator availability/basic function
	if err := testIVerilogTool(); err != nil {
		return fmt.Errorf("iverilog tool check failed: %v", err)
	}
	if err := testVerilatorTool(); err != nil {
		return fmt.Errorf("verilator tool check failed: %v", err)
	}

	// Restore original module name if it was mocked, as f.moduleName is used by workers
	// to find the module *after* mutation (assuming mutation doesn't change the top module name drastically)
	f.moduleName = originalModuleName

	return nil
}

// testIVerilogTool checks if iverilog is installed and runnable.
func testIVerilogTool() error {
	cmd := exec.Command("iverilog", "-V") // Check version as a basic test
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	if err := cmd.Run(); err != nil {
		// Try running without -V if that fails, some versions might not support it well
		cmd = exec.Command("iverilog")
		stderr.Reset()
		cmd.Stderr = &stderr
		if errSimple := cmd.Run(); errSimple != nil &&
			!strings.Contains(stderr.String(), "Usage:") {
			// If running `iverilog` itself fails and doesn't show usage, it's likely not installed/path issue
			return fmt.Errorf(
				"iverilog basic check failed, check installation/PATH: %v - %s",
				errSimple, // Report the error from the simpler command
				stderr.String(),
			)
		}
		// If the simple command ran or showed usage, it's likely installed, even if -V failed.
	}
	log.Println("IVerilog tool found.")
	return nil
}

// testVerilatorTool checks if verilator is installed and runnable.
func testVerilatorTool() error {
	cmd := exec.Command("verilator", "--version") // Check version
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	if err := cmd.Run(); err != nil {
		return fmt.Errorf(
			"verilator basic check failed, check installation/PATH: %v - %s",
			err,
			stderr.String(),
		)
	}
	log.Println("Verilator tool found.")
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

	// Store original ports for comparison in worker
	originalPorts := make(map[string]verilog.Port)
	for _, p := range f.module.Ports {
		originalPorts[p.Name] = p
	}

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
		go f.worker(&wg, testCases, originalPorts)
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
	f.debug.Printf("[%s]: Copying Verilog source file to worker directory", workerID)
	// Only copy the main Verilog file. Testbenches are generated per worker.
	srcPath := filepath.Join(utils.TMP_DIR, verilogFileName)
	dstPath := filepath.Join(workerDir, verilogFileName)

	// Check if source exists
	if _, err := os.Stat(srcPath); os.IsNotExist(err) {
		return fmt.Errorf("[%s]: Source Verilog file %s does not exist", workerID, srcPath)
	}

	if err := utils.CopyFile(srcPath, dstPath); err != nil {
		return fmt.Errorf("failed to copy %s to worker directory: %w", verilogFileName, err)
	}

	// Verify the file was copied successfully
	if fi, err := os.Stat(dstPath); err != nil || fi.Size() == 0 {
		fileSize := int64(0)
		if fi != nil {
			fileSize = fi.Size()
		}
		return fmt.Errorf("[%s]: Verilog file %s not copied correctly, size: %d, error: %v",
			workerID, dstPath, fileSize, err)
	}
	f.debug.Printf("[%s]: Successfully copied %s", workerID, verilogFileName)
	return nil
}

// setupSimulators creates and compiles simulators for the worker.
// Now takes the worker-specific module name.
func (f *Fuzzer) setupSimulators(
	workerID, workerDir, workerModuleName string,
) (simulator.Simulator, simulator.Simulator, error) {
	f.debug.Printf("[%s]: Creating simulators for module %s", workerID, workerModuleName)
	ivsim := simulator.NewIVerilogSimulator(workerDir, f.verbose)
	// Use the potentially mutated module name for Verilator
	vlsim := simulator.NewVerilatorSimulator(workerDir, workerModuleName)

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
// Now takes the worker-specific module.
func (f *Fuzzer) processTestCases(
	workerID, workerDir string,
	ivsim, vlsim simulator.Simulator,
	workerModule *verilog.Module, // Pass the parsed module for this worker
	originalPorts map[string]verilog.Port, // Pass original ports map
	testCases <-chan int,
) {
	for i := range testCases {
		// Pass workerModule and originalPorts to runSingleTest
		f.runSingleTest(workerID, workerDir, ivsim, vlsim, workerModule, originalPorts, i)
	}
}

// runSingleTest executes a single fuzzing test case.
// Now takes the worker-specific module.
func (f *Fuzzer) runSingleTest(
	workerID, workerDir string,
	ivsim, vlsim simulator.Simulator,
	workerModule *verilog.Module, // Use worker-specific module
	originalPorts map[string]verilog.Port, // Original ports for comparison
	testIndex int,
) {
	// Generate test case based on the *original* module structure stored in f.strategy
	testCase := f.strategy.GenerateTestCase(testIndex)
	f.stats.AddTest()

	// --- Add default values for new input ports ---
	for _, port := range workerModule.Ports {
		// Check if it's an input/inout port added by mutation
		_, isOriginal := originalPorts[port.Name]
		if (port.Direction == verilog.INPUT || port.Direction == verilog.INOUT) && !isOriginal {
			// Check if strategy already provided a value (unlikely but possible)
			if _, exists := testCase[port.Name]; !exists {
				// Generate default value '0' padded to the port's width
				defaultValue := strings.Repeat("0", port.Width)
				testCase[port.Name] = defaultValue
				f.debug.Printf("[%s] Test %d: Added default value '%s' for new input port '%s'",
					workerID, testIndex, defaultValue, port.Name)
			}
		}
	}
	// --- End add default values ---

	// Validate against the *worker's* current module structure
	f.validateMultiBitSignals(workerModule, testCase) // Pass workerModule

	// Create test directory within worker directory
	testDir := filepath.Join(workerDir, fmt.Sprintf("test_%d", testIndex))
	if err := os.MkdirAll(testDir, 0o755); err != nil {
		log.Printf("[%s] Failed to create test directory %s: %v", workerID, testDir, err)
		f.stats.AddSimError()
		return
	}
	defer func() {
		if !f.verbose {
			os.RemoveAll(testDir)
		}
	}()

	// Write input files (now includes defaults for new ports)
	if err := writeTestInputs(testDir, testCase); err != nil {
		log.Printf("[%s] Failed to write inputs for test %d: %v", workerID, testIndex, err)
		f.stats.AddSimError()
		return
	}

	// Run both simulators, passing the workerModule
	ivResult, ivSuccess := f.runSimulator("iverilog", ivsim, testDir, workerModule)
	if !ivSuccess {
		log.Printf("[%s] IVerilog simulation failed for test %d", workerID, testIndex)
		return
	}

	vlResult, vlSuccess := f.runSimulator("verilator", vlsim, testDir, workerModule)
	if !vlSuccess {
		log.Printf("[%s] Verilator simulation failed for test %d", workerID, testIndex)
		return
	}

	// Compare results
	mismatch, mismatchDetails := f.compareSimulationResults(ivResult, vlResult)

	if mismatch {
		f.handleMismatch(
			testIndex,
			testDir,
			testCase,
			mismatchDetails,
			workerModule,
		) // Pass workerModule
	}
}

// validateMultiBitSignals checks if multi-bit input values seem reasonable.
// Now takes the module definition to check against.
func (f *Fuzzer) validateMultiBitSignals(module *verilog.Module, testCase map[string]string) {
	for _, port := range module.Ports { // Use the passed module
		if port.Width > 1 && (port.Direction == verilog.INPUT || port.Direction == verilog.INOUT) {
			value, exists := testCase[port.Name]
			if exists {
				// Check if the value is likely a hex string of proper width
				expectedLen := (port.Width + 3) / 4 // Number of expected hex digits
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
			mismatch = true
			mismatchDetails[portName] = fmt.Sprintf(
				"IVerilog=%s, Verilator=MISSING",
				ivValue,
			)
			f.debug.Printf("Warning: Output for port %s missing from Verilator result", portName)
		}
	}

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
// Pass workerModule to accurately determine output ports.
func (f *Fuzzer) handleMismatch(
	testIndex int,
	testDir string,
	testCase map[string]string,
	mismatchDetails map[string]string,
	workerModule *verilog.Module, // Use worker module to know expected outputs
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
	} else {
		for portName := range testCase {
			inputFile := fmt.Sprintf("input_%s.hex", portName)
			src := filepath.Join(testDir, inputFile)
			dst := filepath.Join(mismatchDir, inputFile)
			if err := utils.CopyFile(src, dst); err != nil {
				log.Printf("Failed to copy input file %s: %v", inputFile, err)
			}
		}

		// Copy output files from both simulators
		outputPorts := make(map[string]struct{})
		// Determine output ports from the workerModule definition
		for _, port := range workerModule.Ports {
			if port.Direction == verilog.OUTPUT {
				outputPorts[port.Name] = struct{}{}
			}
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
// Accept originalPorts map
func (f *Fuzzer) worker(
	wg *sync.WaitGroup,
	testCases <-chan int,
	originalPorts map[string]verilog.Port,
) {
	defer wg.Done()

	VerilogFileName := filepath.Base(f.verilogFile)
	workerID := fmt.Sprintf("worker_%d_%d", os.Getpid(), time.Now().UnixNano())

	workerDir, cleanup, err := f.setupWorker(workerID)
	if err != nil {
		log.Printf("Worker setup failed for %s: %v", workerID, err)
		return
	}
	if false {
		defer cleanup()
	}

	if err := f.copyWorkerFiles(workerID, workerDir, VerilogFileName); err != nil {
		log.Printf("Failed to copy files for worker %s: %v", workerID, err)
		return
	}

	workerVerilogPath := filepath.Join(workerDir, VerilogFileName)
	f.debug.Printf("[%s] Attempting mutation on %s", workerID, workerVerilogPath)
	if err := MutateFile(workerVerilogPath); err != nil {
		log.Printf("[%s] Mutation failed: %v. Skipping tests for this worker cycle.", workerID, err)
		f.stats.AddSimError()
		return
	}
	f.debug.Printf("[%s] Mutation applied. Proceeding.", workerID)

	f.debug.Printf("[%s] Parsing potentially mutated Verilog file: %s", workerID, workerVerilogPath)
	workerModule, err := verilog.ParseVerilogFile(workerVerilogPath, f.moduleName)
	if err != nil {
		log.Printf(
			"[%s] Failed to parse mutated Verilog file %s: %v",
			workerID,
			workerVerilogPath,
			err,
		)
		f.stats.AddSimError()
		return
	}
	f.debug.Printf(
		"[%s] Parsed module '%s' with %d ports from worker file.",
		workerID,
		workerModule.Name,
		len(workerModule.Ports),
	)

	f.debug.Printf(
		"[%s] Generating testbenches for module %s in %s",
		workerID,
		workerModule.Name,
		workerDir,
	)
	gen := testgen.NewGenerator(workerModule)
	if err := gen.GenerateTestbenchesInDir(workerDir); err != nil {
		log.Printf("[%s] Failed to generate testbenches: %v", workerID, err)
		f.stats.AddSimError()
		return
	}
	f.debug.Printf("[%s] Testbenches generated.", workerID)

	ivsim, vlsim, err := f.setupSimulators(workerID, workerDir, workerModule.Name)
	if err != nil {
		log.Printf("Simulator setup failed for worker %s: %v", workerID, err)
		return
	}

	f.processTestCases(workerID, workerDir, ivsim, vlsim, workerModule, originalPorts, testCases)
}

// writeTestInputs writes test case input files
func writeTestInputs(testDir string, testCase map[string]string) error {
	for portName, value := range testCase {
		inputPath := filepath.Join(testDir, fmt.Sprintf("input_%s.hex", portName))
		if err := os.WriteFile(inputPath, []byte(value), 0o644); err != nil {
			return fmt.Errorf("failed to write input file %s: %v", inputPath, err)
		}
	}
	return nil
}

// runSimulator executes a simulator and collects output results
// Now takes the worker-specific module to determine output ports.
func (f *Fuzzer) runSimulator(
	simName string,
	sim simulator.Simulator,
	testDir string,
	module *verilog.Module,
) (map[string]string, bool) {
	outputDir := filepath.Join(testDir, simName)
	if err := os.MkdirAll(outputDir, 0o755); err != nil {
		log.Printf("Failed to create output dir %s: %v", outputDir, err)
		f.stats.AddSimError()
		return nil, false
	}

	outputPaths := make(map[string]string)
	for _, port := range module.Ports {
		if port.Direction == verilog.OUTPUT {
			var prefix string
			if simName == "iverilog" {
				prefix = IV_PREFIX
			} else {
				prefix = VL_PREFIX
			}
			outputFile := fmt.Sprintf("%s%s.hex", prefix, port.Name)
			outputPaths[port.Name] = filepath.Join(testDir, outputFile)
		}
	}

	if len(outputPaths) == 0 {
		f.debug.Printf(
			"Warning: No output ports found for module %s in runSimulator (%s)",
			module.Name,
			simName,
		)
	}

	if err := sim.RunTest(testDir, outputPaths); err != nil {
		f.stats.AddSimError()
		return nil, false
	}

	if len(outputPaths) > 0 {
		if err := simulator.VerifyOutputFiles(outputPaths); err != nil {
			log.Printf("Output file verification failed for %s: %v", simName, err)
			f.stats.AddSimError()
			return nil, false
		}
	}

	results, err := simulator.ReadOutputFiles(outputPaths)
	if err != nil {
		log.Printf("Failed to read output files for %s: %v", simName, err)
		f.stats.AddSimError()
		return nil, false
	}

	return results, true
}
