package fuzz

import (
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"strings"
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

func (sch *Scheduler) setupWorker(workerID string) (string, func(), error) {
	workerDir := filepath.Join(utils.TMP_DIR, workerID)
	sch.debug.Debug("[%s] Creating worker directory at %s", workerID, workerDir)
	if err := os.MkdirAll(workerDir, 0o755); err != nil {
		return "", nil, fmt.Errorf("failed to create worker directory %s: %w", workerDir, err)
	}
	cleanup := func() {
		if err := os.RemoveAll(workerDir); err != nil {
			sch.debug.Warn("Failed to clean up worker directory %s: %v", workerDir, err)
		}
		sch.debug.Debug("Cleaned up worker directory: %s", workerDir)
	}
	return workerDir, cleanup, nil
}

func (sch *Scheduler) copyWorkerFiles(workerID, workerDir, verilogFileName string) error {
	srcPath := filepath.Join(utils.TMP_DIR, verilogFileName)
	dstPath := filepath.Join(workerDir, verilogFileName)
	sch.debug.Debug(
		"[%s] Copying Verilog source file `%s` to `%s`",
		workerID,
		srcPath,
		dstPath,
	)
	if _, err := os.Stat(srcPath); os.IsNotExist(err) {
		return fmt.Errorf("[%s] Source Verilog file %s does not exist", workerID, srcPath)
	}
	if err := utils.CopyFile(srcPath, dstPath); err != nil {
		return fmt.Errorf("failed to copy %s to worker directory: %w", verilogFileName, err)
	}
	if fi, err := os.Stat(dstPath); err != nil || fi.Size() == 0 {
		fileSize := int64(0)
		if fi != nil {
			fileSize = fi.Size()
		}
		return fmt.Errorf("[%s] Verilog file %s not copied correctly, size: %d, error: %v",
			workerID, dstPath, fileSize, err)
	}
	sch.debug.Debug("[%s] Successfully copied %s", workerID, verilogFileName)
	return nil
}

// performWorkerAttempt tries to set up and run tests for one worker attempt.
// It returns true if the setup was successful and test processing started, along with any error from setup.
// If setup was successful, the error returned is nil.
// If setup failed, it returns false and the setup error.
func (sch *Scheduler) performWorkerAttempt(
	workerID string,
	testCases <-chan int,
	workerModule *verilog.Module,
	strategy Strategy,
) (setupSuccessful bool, err error) {
	workerDir, cleanupFunc, setupErr := sch.setupWorker(workerID)
	if setupErr != nil {
		return false, fmt.Errorf("worker setup failed for %s: %w", workerID, setupErr)
	}

	attemptCompletelySuccessful := false
	defer func() {
		if cleanupFunc != nil {
			if (sch.verbose > 2 && !attemptCompletelySuccessful) || sch.verbose > 3 {
				sch.debug.Debug(
					"[%s] Preserving worker directory %s (verbose = %d). Attempt success: %t",
					workerID,
					workerDir,
					sch.verbose,
					attemptCompletelySuccessful,
				)
			} else {
				sch.debug.Debug("[%s] Cleaning up worker directory %s. Attempt success: %t", workerID, workerDir, attemptCompletelySuccessful)
				cleanupFunc()
			}
		}
	}()

	if err := sch.copyWorkerFiles(workerID, workerDir, sch.svFile.Name); err != nil {
		return false, fmt.Errorf("failed to copy files for worker %s: %w", workerID, err)
	}

	workerVerilogPath := filepath.Join(workerDir, sch.svFile.Name)
	var svFile *verilog.VerilogFile
	if sch.operation == OpFuzz {
		sch.debug.Debug("[%s] Attempting mutation on %s", workerID, workerVerilogPath)
		if svFile, err = MutateFile(sch.svFile, workerVerilogPath, sch.verbose); err != nil {
			return false, fmt.Errorf("[%s] mutation failed: %w", workerID, err)
		}
		sch.debug.Debug("[%s] Mutation applied. Proceeding.", workerID)
	} else {
		sch.debug.Debug("[%s] Mutation not requested. Proceeding with original file.", workerID)
		fileContent, err := utils.ReadFileContent(workerVerilogPath)
		if err != nil {
			return false, fmt.Errorf("[%s] failed to read Verilog file: %w", workerID, err)
		}
		svFile, err = verilog.ParseVerilog(fileContent, sch.verbose)
		svFile.Name = sch.svFile.Name
		if err != nil {
			return false, fmt.Errorf("[%s] failed to parse Verilog file: %w", workerID, err)
		}
	}

	if err != nil {
		return false, fmt.Errorf("[%s] failed to parse mutated Verilog: %w", workerID, err)
	}
	sch.debug.Debug(
		"[%s] Parsed %d modules from file %s.",
		workerID,
		len(svFile.Modules),
		svFile.Name,
	)

	sch.debug.Debug(
		"[%s] Generating testbenches for module %s in %s",
		workerID,
		workerModule.Name,
		workerDir,
	)
	gen := testgen.NewGenerator(workerModule, svFile.Name)
	if err := gen.GenerateTestbenchesInDir(workerDir); err != nil {
		return false, fmt.Errorf("[%s] failed to generate testbenches: %w", workerID, err)
	}
	sch.debug.Debug("[%s] Testbenches generated.", workerID)

	ivsim, vlsim, err := sch.setupSimulators(workerID, workerDir, workerModule.Name)
	if err != nil {
		if strings.Contains(err.Error(), "One of the compilations failed") {
			if sch.operation == OpFuzz {
				sch.handleCompilationMismatch(workerID, workerModule, err)
				sch.stats.AddMismatch(nil)
			}
			return false, fmt.Errorf(
				"[%s] One of the verilator compilations failed: %w",
				workerID,
				err,
			)
		}
		return false, fmt.Errorf("simulator setup failed for worker %s: %w", workerID, err)
	}

	sch.debug.Debug("[%s] Simulators set up successfully.", workerID)
	sch.debug.Debug(
		"[%s] Starting test case processing for module %s\n    %d test cases\n    %s strategy",
		workerID,
		workerModule.Name,
		len(testCases),
		strategy.Name(),
	)

	errorMap := sch.processTestCases(
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

func (sch *Scheduler) setupSimulators(
	workerID, workerDir, workerModuleName string,
) (simulator.Simulator, simulator.Simulator, error) {
	sch.debug.Debug("[%s] Creating simulators for module %s", workerID, workerModuleName)
	// ivsim := simulator.NewIVerilogSimulator(workerDir, f.verbose)
	vlsim3 := simulator.NewVerilatorSimulator(
		workerDir+"/O3",
		sch.svFile,
		workerModuleName,
		true,
		sch.verbose,
	)
	vlsim0 := simulator.NewVerilatorSimulator(
		workerDir+"/O0",
		sch.svFile,
		workerModuleName,
		false,
		sch.verbose,
	)
	sch.debug.Debug("[%s] Compiling IVerilog simulator", workerID)
	// if err := ivsim.Compile(); err != nil {
	//	return nil, nil, fmt.Errorf("failed to compile IVerilog in worker %s: %w", workerID, err)
	//}
	sch.debug.Debug("[%s] Compiling Verilator simulator", workerID)
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
		// define which is the error
		var err error
		opt := "O0"
		if vl0err != nil {
			err = vl0err
		} else {
			err = vl3err
			opt = "O3"
		}
		sch.debug.Warn(
			"[%s] One of the Verilator compilations failed, %v, %s",
			workerID,
			err,
			opt,
		)
		return nil, nil, fmt.Errorf("[%s] One of the compilations failed: %w, %s",
			workerID,
			err,
			opt,
		)
	}
	return vlsim0, vlsim3, nil
}

func (sch *Scheduler) worker(
	testCases <-chan int,
	moduleToTest *verilog.Module,
	workerNum int,
) error {
	var lastSetupError error
	workerID := fmt.Sprintf("worker_%d_%d", workerNum, time.Now().UnixNano())
	var strategy Strategy
	switch sch.strategyName {
	case "random":
		strategy = &RandomStrategy{}
	case "smart":
		strategy = &SmartStrategy{}
	default:
		return fmt.Errorf("Unknown strategy: %s", sch.strategyName)
	}

	strategy.SetModule(moduleToTest)

	for attempt := 0; attempt < sch.maxAttempts; attempt++ {
		workerCompleteID := fmt.Sprintf(
			"%s_%d",
			workerID,
			attempt,
		)
		sch.debug.Debug(
			"[%s] Starting worker attempt %d/%d",
			workerCompleteID,
			attempt+1,
			sch.maxAttempts,
		)

		setupOk, err := sch.performWorkerAttempt(
			workerCompleteID,
			testCases,
			moduleToTest,
			strategy,
		)

		if setupOk {
			sch.debug.Info("[%s] Worker completed its tasks.", workerID)
			return nil
		}

		// Setup failed for this attempt
		lastSetupError = err
		sch.debug.Warn(
			"[%s] Worker attempt %d/%d failed setup for module %s from file %s",
			workerCompleteID,
			attempt+1,
			sch.maxAttempts,
			moduleToTest.Name,
			sch.svFile.Name,
		)

		if attempt < sch.maxAttempts-1 {
			sch.debug.Info(
				"[%s] Retrying worker initialization after a short delay...",
				workerCompleteID,
			)
			time.Sleep(time.Duration(attempt+1) * time.Second) // Optional backoff
		}
	}

	return fmt.Errorf(
		"[%s] Worker failed to initialize after %d attempts: %v",
		workerID,
		sch.maxAttempts,
		lastSetupError,
	)
}

func (sch *Scheduler) processTestCases(
	workerID, workerDir string,
	ivsim, vlsim simulator.Simulator,
	workerModule *verilog.Module,
	testCases <-chan int,
	strategy Strategy,
) []error {
	errorMap := []error{}
	for i := range testCases {
		err := sch.runSingleTest(workerID, workerDir, ivsim, vlsim, workerModule, i, strategy)
		if err != nil {
			errorMap = append(errorMap, err)
		}
	}
	return errorMap
}

func (sch *Scheduler) runSingleTest(
	workerID, workerDir string,
	ivsim, vlsim simulator.Simulator,
	workerModule *verilog.Module,
	testIndex int,
	strategy Strategy,
) error {
	testCase := strategy.GenerateTestCase(testIndex)
	sch.stats.AddTest()

	for _, port := range workerModule.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			if _, exists := testCase[port.Name]; !exists {
				defaultValue := strings.Repeat("0", port.Width)
				testCase[port.Name] = defaultValue
				sch.debug.Debug("[%s] Test %d: Added default value '%s' for new input port '%s'",
					workerID, testIndex, defaultValue, port.Name)
			}
		}
	}

	relativeTestDir := filepath.Join(workerDir, fmt.Sprintf("test_%d", testIndex))
	testDir, err := filepath.Abs(relativeTestDir)
	if err != nil {
		return fmt.Errorf(
			"[%s] Failed to get absolute path for test directory %s: %v",
			workerID,
			relativeTestDir,
			err,
		)
	}

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

	ivResult, ivErr := sch.runSimulator("iverilog", ivsim, testDir, workerModule)
	vlResult, vlErr := sch.runSimulator("verilator", vlsim, testDir, workerModule)

	if ivErr != nil && vlErr != nil {
		mismatch = true
		return fmt.Errorf(
			"[%s] Both simulations failed for test %d on module %s with errors : \n%s\n%s",
			workerID,
			testIndex,
			workerModule.Name,
			ivErr,
			vlErr,
		)
	}

	mismatch, mismatchDetails := sch.compareSimulationResults(ivResult, vlResult)
	if mismatch && sch.operation == OpFuzz {
		sch.handleMismatch(testIndex, testDir, testCase, mismatchDetails, workerModule)
	}
	return nil
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

func (sch *Scheduler) runSimulator(
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
		sch.debug.Debug(
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
