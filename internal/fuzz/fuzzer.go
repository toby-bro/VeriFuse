package fuzz

import (
	"bytes"
	"context"
	"fmt"
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
	verbose     int
	seed        int64
	debug       *utils.DebugLogger
	verilogFile string
	moduleName  string
	module      *verilog.Module
	mutate      bool
	maxAttempts int
}

// NewFuzzer creates a new fuzzer instance
func NewFuzzer(
	strategy string,
	workers int,
	verbose int,
	seed int64,
	verilogFile string,
	moduleName string,
	mutate bool,
	maxAttempts int,
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
		mutate:      mutate,
		maxAttempts: maxAttempts,
	}

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
func PrepareSVFile(
	initialVerilogFile string,
	mockedVerilogPath string,
	mock bool,
	verbose int,
) error {
	logger := utils.NewDebugLogger(verbose)
	if mock {
		content, err := mocker.MockVerilogFile(initialVerilogFile)
		if err != nil {
			return fmt.Errorf("failed to analyze Verilog file: %v", err)
		}
		if err := utils.WriteFileContent(mockedVerilogPath, content); err != nil {
			return fmt.Errorf("failed to write mocked SV file: %v", err)
		}
		logger.Debug("Created mocked SystemVerilog file: %s", mockedVerilogPath)
	} else {
		if err := utils.CopyFile(initialVerilogFile, mockedVerilogPath); err != nil {
			return fmt.Errorf("failed to copy original Verilog file: %v", err)
		}
	}
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
	if err := utils.EnsureDirs(); err != nil {
		return fmt.Errorf("failed to create directories: %v", err)
	}

	originalModule, err := verilog.ParseVerilogFile(f.verilogFile, f.moduleName)
	if err != nil {
		return fmt.Errorf("failed to parse original Verilog file: %v", err)
	}
	f.module = originalModule

	originalVerilogFile := f.verilogFile
	originalModuleName := f.moduleName

	if mock {
		f.module.Name = addMockedSuffix(originalModule.Name)
		f.verilogFile = addMockedSuffix(f.verilogFile)
		f.moduleName = f.module.Name
	}

	if moduleAwareStrategy, ok := f.strategy.(ModuleAwareStrategy); ok {
		moduleAwareStrategy.SetModule(f.module)
	}

	f.debug.Info("Parsed original module '%s' with %d ports", f.module.Name, len(f.module.Ports))

	verilogFileName := filepath.Base(f.verilogFile)
	verilogPath := filepath.Join(utils.TMP_DIR, verilogFileName)

	sourceFileForPrepare := originalVerilogFile
	if !mock {
		sourceFileForPrepare = f.verilogFile
	}

	if err := PrepareSVFile(sourceFileForPrepare, verilogPath, mock, f.verbose); err != nil {
		return err
	}

	f.debug.Info("Verilog file prepared at %s", verilogPath)

	if err := testIVerilogTool(); err != nil {
		return fmt.Errorf("iverilog tool check failed: %v", err)
	}
	f.debug.Debug("IVerilog tool found.")
	if err := testVerilatorTool(); err != nil {
		return fmt.Errorf("verilator tool check failed: %v", err)
	}
	f.debug.Debug("Verilator tool found.")
	f.moduleName = originalModuleName
	return nil
}

func testIVerilogTool() error {
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

func testVerilatorTool() error {
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

// Run performs the fuzzing
func (f *Fuzzer) Run(numTests int) error {
	f.debug.Info("Starting fuzzing with %d test cases using strategy: %s\n",
		numTests, f.strategy.Name())
	f.debug.Info("Target module: %s with %d ports", f.module.Name, len(f.module.Ports))

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
	f.debug.Info("Module has %d inputs and %d outputs", inputCount, outputCount)

	originalPorts := make(map[string]verilog.Port)
	for _, p := range f.module.Ports {
		originalPorts[p.Name] = p
	}

	var wg sync.WaitGroup // For fuzzing workers
	testCases := make(chan int, f.workers)

	// Progress tracking - pass the worker WaitGroup
	progressTracker := NewProgressTracker(numTests, f.stats, &wg)
	progressTracker.Start()
	defer progressTracker.Stop()

	// Create a context that can be cancelled when workers are done
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel() // Ensure cancel is called to free resources

	for w := 0; w < f.workers; w++ {
		wg.Add(1)
		go f.worker(&wg, testCases, originalPorts)
	}

	var feedingWg sync.WaitGroup
	feedingWg.Add(1)
	go func() {
		defer feedingWg.Done()
		defer close(testCases)

		for i := 0; i < numTests; i++ {
			select {
			case testCases <- i:
			case <-ctx.Done():
				f.debug.Info(
					"Test case feeding cancelled after %d/%d tests (workers finished/terminated or main context cancelled).",
					i,
					numTests,
				)
				return
			}
		}
		f.debug.Info("Successfully fed all %d test cases to the channel.", numTests)
	}()

	wg.Wait()
	cancel()
	feedingWg.Wait()

	f.stats.PrintSummary() // Uses updated PrintSummary

	// Check if any tests were actually run, especially if numTests > 0
	// Message updated to not mention SimErrors
	if numTests > 0 && f.stats.TotalTests == 0 {
		f.debug.Warn("Fuzzing completed, but no test cases were successfully executed.")
		f.debug.Warn("Out of %d test cases requested, %d were run.", numTests, f.stats.TotalTests)
		f.debug.Warn(
			"This often indicates a persistent problem in the test case generation or worker setup phase for all workers.",
		)
		f.debug.Warn(
			"Common causes include: missing resources required by the fuzzing strategy, or other strategy-specific initialization failures leading to simulator compilation errors.",
		)
		f.debug.Warn("Please review logs for worker-specific error messages.")
		return fmt.Errorf(
			"fuzzing finished but no tests were executed out of %d requested; check logs for worker setup or test generation errors",
			numTests,
		)
	}

	if f.stats.Mismatches > 0 {
		f.debug.Info("Found %d mismatches between iverilog and verilator!\n", f.stats.Mismatches)
		return fmt.Errorf("%d mismatches found", f.stats.Mismatches)
	}

	f.debug.Info("No mismatches found after %d tests.\n", numTests)
	return nil
}

func compareOutputValues(ivValue, vlValue string) bool {
	ivNorm := strings.TrimSpace(strings.ToLower(ivValue))
	vlNorm := strings.TrimSpace(strings.ToLower(vlValue))
	if ivNorm == vlNorm {
		return true
	}
	if (ivNorm == "00" && vlNorm == "xx") || (ivNorm == "xx" && vlNorm == "00") {
		return true
	}
	if (ivNorm == "0" && vlNorm == "x") || (ivNorm == "x" && vlNorm == "0") {
		return true
	}
	if len(ivNorm) == len(vlNorm) && ivNorm != vlNorm {
		if strings.Contains(ivNorm, "x") || strings.Contains(vlNorm, "x") {
			equivalent := true
			for i := 0; i < len(ivNorm); i++ {
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
	return false
}

func (f *Fuzzer) setupWorker(workerID string) (string, func(), error) {
	workerDir := filepath.Join(utils.TMP_DIR, workerID)
	f.debug.Debug("[%s]: Creating worker directory at %s", workerID, workerDir)
	if err := os.MkdirAll(workerDir, 0o755); err != nil {
		return "", nil, fmt.Errorf("failed to create worker directory %s: %w", workerDir, err)
	}
	cleanup := func() {
		if err := os.RemoveAll(workerDir); err != nil {
			f.debug.Warn("Failed to clean up worker directory %s: %v", workerDir, err)
		}
		f.debug.Debug("Cleaned up worker directory: %s", workerDir)
	}
	return workerDir, cleanup, nil
}

func (f *Fuzzer) copyWorkerFiles(workerID, workerDir, verilogFileName string) error {
	f.debug.Debug("[%s]: Copying Verilog source file to worker directory", workerID)
	srcPath := filepath.Join(utils.TMP_DIR, verilogFileName)
	dstPath := filepath.Join(workerDir, verilogFileName)
	if _, err := os.Stat(srcPath); os.IsNotExist(err) {
		return fmt.Errorf("[%s]: Source Verilog file %s does not exist", workerID, srcPath)
	}
	if err := utils.CopyFile(srcPath, dstPath); err != nil {
		return fmt.Errorf("failed to copy %s to worker directory: %w", verilogFileName, err)
	}
	if fi, err := os.Stat(dstPath); err != nil || fi.Size() == 0 {
		fileSize := int64(0)
		if fi != nil {
			fileSize = fi.Size()
		}
		return fmt.Errorf("[%s]: Verilog file %s not copied correctly, size: %d, error: %v",
			workerID, dstPath, fileSize, err)
	}
	f.debug.Debug("[%s]: Successfully copied %s", workerID, verilogFileName)
	return nil
}

func (f *Fuzzer) setupSimulators(
	workerID, workerDir, workerModuleName string,
) (simulator.Simulator, simulator.Simulator, error) {
	f.debug.Debug("[%s]: Creating simulators for module %s", workerID, workerModuleName)
	// ivsim := simulator.NewIVerilogSimulator(workerDir, f.verbose)
	vlsim3 := simulator.NewVerilatorSimulator(workerDir, workerModuleName, true, f.verbose)
	vlsim0 := simulator.NewVerilatorSimulator(workerDir, workerModuleName, false, f.verbose)
	f.debug.Debug("[%s]: Compiling IVerilog simulator", workerID)
	//if err := ivsim.Compile(); err != nil {
	//	return nil, nil, fmt.Errorf("failed to compile IVerilog in worker %s: %w", workerID, err)
	//}
	f.debug.Debug("[%s]: Compiling Verilator simulator", workerID)
	if err := vlsim0.Compile(); err != nil {
		return nil, nil, fmt.Errorf("failed to compile Verilator in worker %s: %w", workerID, err)
	}
	if err := vlsim3.Compile(); err != nil {
		return nil, nil, fmt.Errorf("failed to compile Verilator in worker %s: %w", workerID, err)
	}
	return vlsim0, vlsim3, nil
}

func (f *Fuzzer) processTestCases(
	workerID, workerDir string,
	ivsim, vlsim simulator.Simulator,
	workerModule *verilog.Module,
	originalPorts map[string]verilog.Port,
	testCases <-chan int,
) {
	for i := range testCases {
		f.runSingleTest(workerID, workerDir, ivsim, vlsim, workerModule, originalPorts, i)
	}
}

func (f *Fuzzer) runSingleTest(
	workerID, workerDir string,
	ivsim, vlsim simulator.Simulator,
	workerModule *verilog.Module,
	originalPorts map[string]verilog.Port,
	testIndex int,
) {
	testCase := f.strategy.GenerateTestCase(testIndex)
	f.stats.AddTest()

	for _, port := range workerModule.Ports {
		_, isOriginal := originalPorts[port.Name]
		if (port.Direction == verilog.INPUT || port.Direction == verilog.INOUT) && !isOriginal {
			if _, exists := testCase[port.Name]; !exists {
				defaultValue := strings.Repeat("0", port.Width)
				testCase[port.Name] = defaultValue
				f.debug.Debug("[%s] Test %d: Added default value '%s' for new input port '%s'",
					workerID, testIndex, defaultValue, port.Name)
			}
		}
	}

	f.validateMultiBitSignals(workerModule, testCase)

	testDir := filepath.Join(workerDir, fmt.Sprintf("test_%d", testIndex))
	if err := os.MkdirAll(testDir, 0o755); err != nil {
		f.debug.Fatal("[%s] Failed to create test directory %s: %v", workerID, testDir, err)
		return
	}
	defer func() {
		os.RemoveAll(testDir)
	}()

	if err := writeTestInputs(testDir, testCase); err != nil {
		f.debug.Fatal("[%s] Failed to write inputs for test %d: %v", workerID, testIndex, err)
		return
	}

	ivResult, ivSuccess := f.runSimulator("iverilog", ivsim, testDir, workerModule)
	if !ivSuccess {
		f.debug.Error("[%s] IVerilog simulation failed for test %d", workerID, testIndex)
		return
	}

	vlResult, vlSuccess := f.runSimulator("verilator", vlsim, testDir, workerModule)
	if !vlSuccess {
		f.debug.Error("[%s] Verilator simulation failed for test %d", workerID, testIndex)
		return
	}

	mismatch, mismatchDetails := f.compareSimulationResults(ivResult, vlResult)
	if mismatch {
		f.handleMismatch(testIndex, testDir, testCase, mismatchDetails, workerModule)
	}
}

func (f *Fuzzer) validateMultiBitSignals(module *verilog.Module, testCase map[string]string) {
	for _, port := range module.Ports {
		if port.Width > 1 && (port.Direction == verilog.INPUT || port.Direction == verilog.INOUT) {
			value, exists := testCase[port.Name]
			if exists {
				expectedLen := (port.Width + 3) / 4
				if len(value) > 0 && len(value) < expectedLen {
					f.debug.Debug(
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
			mismatchDetails[portName] = fmt.Sprintf("IVerilog=%s, Verilator=MISSING", ivValue)
			f.debug.Debug("Warning: Output for port %s missing from Verilator result", portName)
		}
	}
	for portName, vlValue := range vlResult {
		if _, exists := ivResult[portName]; !exists {
			mismatch = true
			mismatchDetails[portName] = "IVerilog=MISSING, Verilator=" + vlValue
			f.debug.Debug("Warning: Output for port %s missing from IVerilog result", portName)
		}
	}
	return mismatch, mismatchDetails
}

func (f *Fuzzer) handleMismatch(
	testIndex int,
	testDir string,
	testCase map[string]string,
	mismatchDetails map[string]string,
	workerModule *verilog.Module,
) {
	f.debug.Info("Mismatch found in test %d:\n", testIndex)
	f.debug.Info("Inputs:\n")
	for portName, value := range testCase {
		f.debug.Info("  %s = %s\n", portName, value)
	}
	f.debug.Info("Mismatched outputs:\n")
	for portName, detail := range mismatchDetails {
		f.debug.Info("  %s: %s\n", portName, detail)
	}
	mismatchDir := filepath.Join(utils.MISMATCHES_DIR, fmt.Sprintf("mismatch_%d", testIndex))
	if err := os.MkdirAll(mismatchDir, 0o755); err != nil {
		f.debug.Error("Failed to create mismatch directory %s: %v", mismatchDir, err)
	} else {
		for portName := range testCase {
			inputFile := fmt.Sprintf("input_%s.hex", portName)
			src := filepath.Join(testDir, inputFile)
			dst := filepath.Join(mismatchDir, inputFile)
			if err := utils.CopyFile(src, dst); err != nil {
				f.debug.Error("Failed to copy input file %s: %v", inputFile, err)
			}
		}
		outputPorts := make(map[string]struct{})
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
					f.debug.Error("Failed to copy IVerilog output file %s: %v", ivFile, err)
				}
			}
			if utils.FileExists(vlFile) {
				dst := filepath.Join(mismatchDir, fmt.Sprintf("%s%s.hex", VL_PREFIX, portName))
				if err := utils.CopyFile(vlFile, dst); err != nil {
					f.debug.Error("Failed to copy Verilator output file %s: %v", vlFile, err)
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
			f.debug.Error("Failed to create mismatch summary file %s: %v", summaryPath, err)
		}
	}
	f.stats.AddMismatch(testCase)
}

// performWorkerAttempt tries to set up and run tests for one worker attempt.
// It returns true if the setup was successful and test processing started, along with any error from setup.
// If setup was successful, the error returned is nil.
// If setup failed, it returns false and the setup error.
func (f *Fuzzer) performWorkerAttempt(
	workerID string,
	testCases <-chan int,
	originalPorts map[string]verilog.Port,
) (setupSuccessful bool, err error) {
	VerilogFileName := filepath.Base(f.verilogFile)
	workerDir, cleanupFunc, setupErr := f.setupWorker(workerID)
	if setupErr != nil {
		return false, fmt.Errorf("worker setup failed for %s: %w", workerID, setupErr)
	}

	var attemptCompletelySuccessful bool = false
	defer func() {
		if cleanupFunc != nil {
			if (f.verbose > 2 && !attemptCompletelySuccessful) || f.verbose > 3 {
				// Preserve directory if verbose > 3
				f.debug.Debug(
					"[%s] Preserving worker directory %s (verbose = %d). Attempt success: %t",
					workerID,
					workerDir,
					f.verbose,
					attemptCompletelySuccessful,
				)
			} else {
				// Cleanup directory if verbose <= 3
				f.debug.Debug("[%s] Cleaning up worker directory %s. Attempt success: %t", workerID, workerDir, attemptCompletelySuccessful)
				cleanupFunc()
			}
		}
	}()

	if err := f.copyWorkerFiles(workerID, workerDir, VerilogFileName); err != nil {
		return false, fmt.Errorf("failed to copy files for worker %s: %w", workerID, err)
	}

	workerVerilogPath := filepath.Join(workerDir, VerilogFileName)

	if f.mutate {
		f.debug.Debug("[%s] Attempting mutation on %s", workerID, workerVerilogPath)
		if err := MutateFile(workerVerilogPath, f.verbose); err != nil {
			return false, fmt.Errorf("[%s] mutation failed: %w", workerID, err)
		}
		f.debug.Debug("[%s] Mutation applied. Proceeding.", workerID)
	} else {
		f.debug.Debug("[%s] Mutation not requested. Proceeding with original file.", workerID)
	}

	f.debug.Debug("[%s] Parsing potentially mutated Verilog file: %s", workerID, workerVerilogPath)
	workerModule, err := verilog.ParseVerilogFile(workerVerilogPath, f.moduleName)
	if err != nil {
		return false, fmt.Errorf("[%s] failed to parse mutated Verilog: %w", workerID, err)
	}
	f.debug.Debug(
		"[%s] Parsed module '%s' with %d ports from worker file.",
		workerID,
		workerModule.Name,
		len(workerModule.Ports),
	)

	f.debug.Debug(
		"[%s] Generating testbenches for module %s in %s",
		workerID,
		workerModule.Name,
		workerDir,
	)
	gen := testgen.NewGenerator(workerModule)
	if err := gen.GenerateTestbenchesInDir(workerDir); err != nil {
		return false, fmt.Errorf("[%s] failed to generate testbenches: %w", workerID, err)
	}
	f.debug.Info("[%s] Testbenches generated.", workerID)

	ivsim, vlsim, err := f.setupSimulators(workerID, workerDir, workerModule.Name)
	if err != nil {
		return false, fmt.Errorf("simulator setup failed for worker %s: %w", workerID, err)
	}

	f.processTestCases(workerID, workerDir, ivsim, vlsim, workerModule, originalPorts, testCases)
	attemptCompletelySuccessful = true // Mark as successful for cleanup logic
	return true, nil                   // Setup successful, processTestCases completed.
}

func (f *Fuzzer) worker(
	wg *sync.WaitGroup,
	testCases <-chan int,
	originalPorts map[string]verilog.Port,
) {
	defer wg.Done()

	var lastSetupError error
	workerID := fmt.Sprintf("worker_%d", time.Now().UnixNano())

	for attempt := 0; attempt < f.maxAttempts; attempt++ {
		// workerCompleteID must be unique per attempt. Using PID, time, and attempt number.
		workerCompleteID := fmt.Sprintf(
			"%s_%d",
			workerID,
			attempt,
		)

		setupOk, err := f.performWorkerAttempt(workerCompleteID, testCases, originalPorts)

		if setupOk {
			f.debug.Info("[%s] Worker completed its tasks.", workerID)
			return // Worker's job is done for this goroutine.
		}

		// Setup failed for this attempt
		lastSetupError = err
		f.debug.Warn(
			"[%s] Worker attempt %d/%d failed setup",
			workerCompleteID,
			attempt+1,
			f.maxAttempts,
		)

		if attempt < f.maxAttempts-1 {
			f.debug.Info(
				"[%s] Retrying worker initialization after a short delay...",
				workerCompleteID,
			)
			time.Sleep(time.Duration(attempt+1) * time.Second) // Optional backoff
		}
	}

	f.debug.Error(
		"Worker failed to initialize permanently after %d attempts. Last error: %v.",
		f.maxAttempts,
		lastSetupError,
	)
	f.debug.Error("[%s] Slot will be lost", workerID)
}

func writeTestInputs(testDir string, testCase map[string]string) error {
	for portName, value := range testCase {
		inputPath := filepath.Join(testDir, fmt.Sprintf("input_%s.hex", portName))
		if err := os.WriteFile(inputPath, []byte(value), 0o644); err != nil {
			return fmt.Errorf("failed to write input file %s: %v", inputPath, err)
		}
	}
	return nil
}

func (f *Fuzzer) runSimulator(
	simName string,
	sim simulator.Simulator,
	testDir string,
	module *verilog.Module,
) (map[string]string, bool) {
	outputDir := filepath.Join(testDir, simName)
	if err := os.MkdirAll(outputDir, 0o755); err != nil {
		f.debug.Error("Failed to create output dir %s: %v", outputDir, err)
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
		f.debug.Debug(
			"Warning: No output ports found for module %s in runSimulator (%s)",
			module.Name,
			simName,
		)
	}

	if err := sim.RunTest(testDir, outputPaths); err != nil {
		return nil, false
	}

	if len(outputPaths) > 0 {
		if err := simulator.VerifyOutputFiles(outputPaths); err != nil {
			f.debug.Error("Output file verification failed for %s: %v", simName, err)
			return nil, false
		}
	}

	results, err := simulator.ReadOutputFiles(outputPaths)
	if err != nil {
		f.debug.Error("Failed to read output files for %s: %v", simName, err)
		return nil, false
	}
	return results, true
}
