package fuzz

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"time"

	"github.com/toby-bro/pfuzz/internal/simulator"
	"github.com/toby-bro/pfuzz/internal/testgen"
	"github.com/toby-bro/pfuzz/internal/verilog"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

const (
	IV_PREFIX = "iv_"
	VL_PREFIX = "vl_"
)

type Fuzzer struct {
	stats        *Stats
	strategyName string
	workers      int
	verbose      int
	seed         int64
	debug        *utils.DebugLogger
	svFile       *verilog.VerilogFile
	mutate       bool
	maxAttempts  int
}

func NewFuzzer(
	strategy string,
	workers int,
	verbose int,
	seed int64,
	fileName string,
	mutate bool,
	maxAttempts int,
) *Fuzzer {
	fuzzer := &Fuzzer{
		stats:        NewStats(),
		workers:      workers,
		verbose:      verbose,
		seed:         seed,
		debug:        utils.NewDebugLogger(verbose),
		mutate:       mutate,
		maxAttempts:  maxAttempts,
		strategyName: strategy,
	}

	fuzzer.svFile = &verilog.VerilogFile{
		Name: fileName,
	}
	return fuzzer
}

func (f *Fuzzer) Setup() error {
	if err := utils.EnsureDirs(); err != nil {
		return fmt.Errorf("failed to create directories: %v", err)
	}

	fileName := f.svFile.Name

	fileContent, err := utils.ReadFileContent(fileName)
	if err != nil {
		f.debug.Fatal("Failed to read file %s: %v", fileName, err)
	}
	f.svFile, err = verilog.ParseVerilog(fileContent, f.verbose)
	if err != nil {
		f.debug.Fatal("Failed to parse file %s: %v", fileName, err)
	}
	f.svFile.Name = filepath.Base(fileName)

	verilogPath := filepath.Join(utils.TMP_DIR, filepath.Base(fileName))
	f.debug.Debug("Copying original Verilog file `%s` to `%s`", fileName, verilogPath)

	if err := utils.CopyFile(fileName, verilogPath); err != nil {
		return fmt.Errorf("failed to copy original Verilog file: %v", err)
	}

	if _, err := os.Stat(verilogPath); os.IsNotExist(err) {
		return fmt.Errorf("copied Verilog file does not exist: %v", err)
	}

	if err := testIVerilogTool(); err != nil {
		return fmt.Errorf("iverilog tool check failed: %v", err)
	}
	f.debug.Debug("IVerilog tool found.")
	if err := testVerilatorTool(); err != nil {
		return fmt.Errorf("verilator tool check failed: %v", err)
	}
	f.debug.Debug("Verilator tool found.")
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

func (f *Fuzzer) Run(numTests int) error {
	f.debug.Info("Starting fuzzing with %d test cases using strategy: %s",
		numTests, f.strategyName)
	f.debug.Info("Target file: %s with %d modules", f.svFile.Name, len(f.svFile.Modules))

	if len(f.svFile.Modules) == 0 {
		return errors.New("no modules found in the provided Verilog file")
	}

	var wg sync.WaitGroup
	testCases := make(chan int, f.workers)
	errChan := make(chan error, f.workers)

	if f.mutate {
		progressTracker := NewProgressTracker(numTests, f.stats, &wg)
		progressTracker.Start()
		defer progressTracker.Stop()
	}
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	moduleNames := make([]string, len(f.svFile.Modules))
	ic := 0
	for _, module := range f.svFile.Modules {
		moduleNames[ic] = module.Name
		ic++
	}

	// TODO: #19 make a channel of modules so as to be sure to test them all out
	for w := 0; w < f.workers; w++ {
		wg.Add(1)
		workerIdx := w
		go func(idx int, mod *verilog.Module) {
			defer wg.Done()
			if err := f.worker(testCases, mod); err != nil {
				errChan <- fmt.Errorf("worker %d (module %s) error: %w", idx, mod.Name, err)
			}
		}(workerIdx, f.svFile.Modules[moduleNames[workerIdx%len(moduleNames)]])
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
	close(errChan)

	var allWorkerErrors []error
	for err := range errChan {
		allWorkerErrors = append(allWorkerErrors, err)
	}
	if len(allWorkerErrors) > 0 {
		f.debug.Error("Fuzzing completed with %d worker error(s):", len(allWorkerErrors))
		for _, we := range allWorkerErrors {
			f.debug.Error("%s", we)
		}
	} else if !f.mutate {
		fmt.Printf("%s[+] File `%s` checked successfully, modules seem valid.%s\n", utils.ColorGreen, f.svFile.Name, utils.ColorReset)
	}

	if f.mutate {
		f.stats.PrintSummary()
	}

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

	if f.stats.Mismatches > 0 && f.mutate {
		f.debug.Info("Found %d mismatches between iverilog and verilator!", f.stats.Mismatches)
		return fmt.Errorf("%d mismatches found", f.stats.Mismatches)
	}

	if len(allWorkerErrors) > 0 {
		return fmt.Errorf(
			"fuzzing failed due to %d worker errors; first: %w",
			len(allWorkerErrors),
			allWorkerErrors[0],
		)
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
	srcPath := filepath.Join(utils.TMP_DIR, verilogFileName)
	dstPath := filepath.Join(workerDir, verilogFileName)
	f.debug.Debug(
		"[%s]: Copying Verilog source file `%s` to `%s`",
		workerID,
		srcPath,
		dstPath,
	)
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
	vlsim3 := simulator.NewVerilatorSimulator(
		workerDir+"/O3",
		f.svFile,
		workerModuleName,
		true,
		f.verbose,
	)
	vlsim0 := simulator.NewVerilatorSimulator(
		workerDir+"/O0",
		f.svFile,
		workerModuleName,
		false,
		f.verbose,
	)
	f.debug.Debug("[%s]: Compiling IVerilog simulator", workerID)
	// if err := ivsim.Compile(); err != nil {
	//	return nil, nil, fmt.Errorf("failed to compile IVerilog in worker %s: %w", workerID, err)
	//}
	f.debug.Debug("[%s]: Compiling Verilator simulator", workerID)
	vl0err := vlsim0.Compile()
	vl3err := vlsim3.Compile()
	if vl0err != nil && vl3err != nil {
		return nil, nil, fmt.Errorf(
			"Both Verilator compilations failed in worker %s: %w, %w",
			workerID,
			vl0err,
			vl3err,
		)
	}
	if vl0err != nil || vl3err != nil {
		f.debug.Warn(
			"[%s]: One of the Verilator compilations failed, Continuing: %v, %v",
			workerID,
			vl0err,
			vl3err,
		)
	}
	return vlsim0, vlsim3, nil
}

func (f *Fuzzer) processTestCases(
	workerID, workerDir string,
	ivsim, vlsim simulator.Simulator,
	workerModule *verilog.Module,
	testCases <-chan int,
	strategy Strategy,
) []error {
	errorMap := []error{}
	for i := range testCases {
		err := f.runSingleTest(workerID, workerDir, ivsim, vlsim, workerModule, i, strategy)
		if err != nil {
			errorMap = append(errorMap, err)
		}
	}
	return errorMap
}

func (f *Fuzzer) runSingleTest(
	workerID, workerDir string,
	ivsim, vlsim simulator.Simulator,
	workerModule *verilog.Module,
	testIndex int,
	strategy Strategy,
) error {
	testCase := strategy.GenerateTestCase(testIndex)
	f.stats.AddTest()

	for _, port := range workerModule.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
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
		return fmt.Errorf("[%s] Failed to create test directory %s: %v", workerID, testDir, err)
	}
	mismatch := false
	defer func() {
		if !mismatch {
			os.RemoveAll(testDir)
		}
	}()

	if err := writeTestInputs(testDir, testCase); err != nil {
		return fmt.Errorf("[%s] Failed to write inputs for test %d: %v", workerID, testIndex, err)
	}

	ivResult, ivErr := f.runSimulator("iverilog", ivsim, testDir, workerModule)
	vlResult, vlErr := f.runSimulator("verilator", vlsim, testDir, workerModule)

	if ivErr != nil && vlErr != nil {
		return fmt.Errorf(
			"[%s] Both simulations failed for test %d on module %s with errors : \n%s\n%s",
			workerID,
			testIndex,
			workerModule.Name,
			ivErr,
			vlErr,
		)
	}

	mismatch, mismatchDetails := f.compareSimulationResults(ivResult, vlResult)
	if mismatch {
		f.handleMismatch(testIndex, testDir, testCase, mismatchDetails, workerModule)
	}
	return nil
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
	f.debug.Info(
		"[%s] Mismatch found in test %d: for module %s",
		testDir,
		testIndex,
		workerModule.Name,
	)
	f.debug.Info("Inputs:")
	for portName, value := range testCase {
		f.debug.Info("  %s = %s", portName, value)
	}
	f.debug.Info("Mismatched outputs:")
	for portName, detail := range mismatchDetails {
		f.debug.Info("  %s: %s", portName, detail)
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
	os.RemoveAll(testDir)
	f.stats.AddMismatch(testCase)
}

// performWorkerAttempt tries to set up and run tests for one worker attempt.
// It returns true if the setup was successful and test processing started, along with any error from setup.
// If setup was successful, the error returned is nil.
// If setup failed, it returns false and the setup error.
func (f *Fuzzer) performWorkerAttempt(
	workerID string,
	testCases <-chan int,
	workerModule *verilog.Module,
	strategy Strategy,
) (setupSuccessful bool, err error) {
	workerDir, cleanupFunc, setupErr := f.setupWorker(workerID)
	if setupErr != nil {
		return false, fmt.Errorf("worker setup failed for %s: %w", workerID, setupErr)
	}

	attemptCompletelySuccessful := false
	defer func() {
		if cleanupFunc != nil {
			if (f.verbose > 2 && !attemptCompletelySuccessful) || f.verbose > 3 {
				f.debug.Debug(
					"[%s] Preserving worker directory %s (verbose = %d). Attempt success: %t",
					workerID,
					workerDir,
					f.verbose,
					attemptCompletelySuccessful,
				)
			} else {
				f.debug.Debug("[%s] Cleaning up worker directory %s. Attempt success: %t", workerID, workerDir, attemptCompletelySuccessful)
				cleanupFunc()
			}
		}
	}()

	if err := f.copyWorkerFiles(workerID, workerDir, f.svFile.Name); err != nil {
		return false, fmt.Errorf("failed to copy files for worker %s: %w", workerID, err)
	}

	workerVerilogPath := filepath.Join(workerDir, f.svFile.Name)
	var svFile *verilog.VerilogFile
	if f.mutate {
		f.debug.Debug("[%s] Attempting mutation on %s", workerID, workerVerilogPath)
		if svFile, err = MutateFile(f.svFile, workerVerilogPath, f.verbose); err != nil {
			return false, fmt.Errorf("[%s] mutation failed: %w", workerID, err)
		}
		f.debug.Debug("[%s] Mutation applied. Proceeding.", workerID)
	} else {
		f.debug.Debug("[%s] Mutation not requested. Proceeding with original file.", workerID)
		fileContent, err := utils.ReadFileContent(workerVerilogPath)
		if err != nil {
			return false, fmt.Errorf("[%s] failed to read Verilog file: %w", workerID, err)
		}
		svFile, err = verilog.ParseVerilog(fileContent, f.verbose)
		svFile.Name = f.svFile.Name
		if err != nil {
			return false, fmt.Errorf("[%s] failed to parse Verilog file: %w", workerID, err)
		}
	}

	if err != nil {
		return false, fmt.Errorf("[%s] failed to parse mutated Verilog: %w", workerID, err)
	}
	f.debug.Debug(
		"[%s] Parsed %d modules from worker file.",
		workerID,
		len(svFile.Modules),
	)

	f.debug.Debug(
		"[%s] Generating testbenches for module %s in %s",
		workerID,
		workerModule.Name,
		workerDir,
	)
	gen := testgen.NewGenerator(workerModule, svFile.Name)
	if err := gen.GenerateTestbenchesInDir(workerDir); err != nil {
		return false, fmt.Errorf("[%s] failed to generate testbenches: %w", workerID, err)
	}
	f.debug.Info("[%s] Testbenches generated.", workerID)

	ivsim, vlsim, err := f.setupSimulators(workerID, workerDir, workerModule.Name)
	if err != nil {
		return false, fmt.Errorf("simulator setup failed for worker %s: %w", workerID, err)
	}

	errorMap := f.processTestCases(
		workerID,
		workerDir,
		ivsim,
		vlsim,
		workerModule,
		testCases,
		strategy,
	)
	if len(errorMap) != 0 {
		errStr := errors.New("")
		for _, err := range errorMap {
			errStr = fmt.Errorf("%s\n%s", errStr, err)
		}
		return false, errStr
	}
	attemptCompletelySuccessful = true // Mark as successful for cleanup logic
	return true, nil
}

func (f *Fuzzer) worker(
	testCases <-chan int,
	moduleToTest *verilog.Module,
) error {
	var lastSetupError error
	workerID := fmt.Sprintf("worker_%d", time.Now().UnixNano())
	var strategy Strategy
	switch f.strategyName {
	case "random":
		strategy = &RandomStrategy{}
	case "smart":
		strategy = &SmartStrategy{}
	default:
		return fmt.Errorf("Unknown strategy: %s", f.strategyName)
	}

	strategy.SetModule(moduleToTest)

	for attempt := 0; attempt < f.maxAttempts; attempt++ {
		workerCompleteID := fmt.Sprintf(
			"%s_%d",
			workerID,
			attempt,
		)

		setupOk, err := f.performWorkerAttempt(workerCompleteID, testCases, moduleToTest, strategy)

		if setupOk {
			f.debug.Info("[%s] Worker completed its tasks.", workerID)
			return nil
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

	return fmt.Errorf(
		"[%s] Worker failed to initialize after %d attempts: %v",
		workerID,
		f.maxAttempts,
		lastSetupError,
	)
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
) (map[string]string, error) {
	outputDir := filepath.Join(testDir, simName)
	if err := os.MkdirAll(outputDir, 0o755); err != nil {
		return nil, fmt.Errorf("failed to create output dir %s: %v", outputDir, err)
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
		return nil, fmt.Errorf("failed to run %s: %v", simName, err)
	}

	if len(outputPaths) > 0 {
		if err := simulator.VerifyOutputFiles(outputPaths); err != nil {
			return nil, fmt.Errorf(
				"Output file verification failed for %s: %v",
				simName,
				err,
			)
		}
	}

	results, err := simulator.ReadOutputFiles(outputPaths)
	if err != nil {
		return nil, fmt.Errorf("failed to read output files for %s: %v", simName, err)
	}
	return results, nil
}
