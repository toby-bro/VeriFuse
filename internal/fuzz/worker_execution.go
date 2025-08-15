package fuzz

import (
	"context"
	"fmt"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"sync"

	"github.com/toby-bro/pfuzz/internal/simulator"
	"github.com/toby-bro/pfuzz/pkg/verilog"
)

func (sch *Scheduler) processSingleTestCase(
	ctx context.Context,
	workerID, workerDir string,
	sims []*SimInstance,
	workerModule *verilog.Module,
	i int,
	strategy Strategy,
	errorMu *sync.Mutex,
	errorCollector *[]error,
) {
	testSpecificDir := filepath.Join(workerDir, fmt.Sprintf("test_%d", i))
	if err := os.MkdirAll(testSpecificDir, 0o755); err != nil {
		err := fmt.Errorf(
			"[%s] failed to create test directory %s: %w",
			workerID,
			testSpecificDir,
			err,
		)
		sch.debug.Error(err.Error())
		errorMu.Lock()
		*errorCollector = append(*errorCollector, err)
		errorMu.Unlock()
		return
	}

	err := sch.runSingleTest(ctx, workerID, testSpecificDir, sims, workerModule, i, strategy)
	if err != nil {
		sch.debug.Error("[%s] Test %d failed: %v", workerID, i, err)
		errorMu.Lock()
		*errorCollector = append(*errorCollector, err)
		errorMu.Unlock()
	}
}

func (sch *Scheduler) processTestCases(
	ctx context.Context,
	workerID, workerDir string,
	sims []*SimInstance, // Changed from ivsim, vlsim
	workerModule *verilog.Module,
	testCases <-chan int,
	strategy Strategy,
) []error {
	var errorCollector []error
	var errorMu sync.Mutex
	workerIDSplits := strings.Split(workerID, "_")
	var initialTestIndex int
	if len(workerIDSplits) > 1 {
		var err error
		initialTestIndex, err = strconv.Atoi(workerIDSplits[1])
		if err != nil {
			sch.debug.Error("Failed to parse workerID index from %q: %v", workerID, err)
			initialTestIndex = 0
		}
	} else {
		initialTestIndex = 0
	}
	sch.processSingleTestCase(
		ctx,
		workerID,
		workerDir,
		sims,
		workerModule,
		initialTestIndex,
		strategy,
		&errorMu,
		&errorCollector,
	)

	for i := range testCases {
		sch.processSingleTestCase(
			ctx,
			workerID,
			workerDir,
			sims,
			workerModule,
			i,
			strategy,
			&errorMu,
			&errorCollector,
		)
	}
	return errorCollector
}

// generateAndPrepareInputs handles test case generation and writing input files.
func (sch *Scheduler) generateAndPrepareInputs(
	workerID, testSpecificDir string,
	workerModule *verilog.Module,
	testIndex int,
	strategy Strategy,
) (map[*verilog.Port]string, error) {
	testCase := strategy.GenerateTestCase(testIndex)
	sch.stats.AddTest()

	for _, port := range workerModule.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			if _, exists := testCase[port]; !exists {
				// defaultValue := strings.Repeat("0", port.Width) // Old binary string
				defaultValue := "0" // New: "0" is a valid hex representation of zero for any width
				testCase[port] = defaultValue
				sch.debug.Debug("[%s] Test %d: Added default value '%s' for new input port '%s'",
					workerID, testIndex, defaultValue, port.Name)
			}
		}
	}

	if err := writeTestInputs(testSpecificDir, testCase); err != nil {
		return nil, fmt.Errorf("failed to write inputs: %w", err)
	}
	return testCase, nil
}

// executeSimulatorsConcurrently manages the concurrent execution of different simulators.
func (sch *Scheduler) executeSimulatorsConcurrently(
	ctx context.Context,
	workerID, testSpecificDir string,
	sims []*SimInstance,
	workerModule *verilog.Module,
	testIndex int,
) (map[*SimInstance]map[*verilog.Port]string, map[*SimInstance]error) {
	simResults := make(map[*SimInstance]map[*verilog.Port]string) // simName -> {portName -> value}
	simErrors := make(map[*SimInstance]error)                     // simName -> error
	var resultsMu sync.Mutex
	var wg sync.WaitGroup

	sch.debug.Debug("[%s] Test %d: Running simulators concurrently", workerID, testIndex)

	for _, simInstance := range sims {
		wg.Add(1)
		go func(si *SimInstance) {
			defer wg.Done()
			sch.debug.Debug(
				"[%s] Test %d: Running simulator %s",
				workerID,
				testIndex,
				si,
			)

			currentSimOutputPaths := make(map[*verilog.Port]string)
			for _, port := range workerModule.Ports {
				if port.Direction == verilog.OUTPUT {
					outputFile := fmt.Sprintf("%s_%s.hex", si, port.Name)
					currentSimOutputPaths[port] = filepath.Join(testSpecificDir, outputFile)
				}
			}

			results, err := sch.runSimulator(
				ctx,
				si.Simulator,
				testSpecificDir,
				currentSimOutputPaths,
			)
			resultsMu.Lock()
			if err != nil {
				simErrors[si] = err
				sch.debug.Warn(
					"[%s] Test %d: Simulator %s failed: %v",
					workerID,
					testIndex,
					si,
					err,
				)
			} else {
				simResults[si] = results
				sch.debug.Debug("[%s] Test %d: Simulator %s completed.", workerID, testIndex, si)
			}
			resultsMu.Unlock()
		}(simInstance)
	}
	wg.Wait()
	return simResults, simErrors
}

// detectAndHandleMismatches compares simulator outputs and handles any discrepancies.
// It returns true if a mismatch was detected and handled, false otherwise.
// An error is returned for critical issues during mismatch processing or if all simulators failed.
func (sch *Scheduler) detectAndHandleMismatches(
	workerID, testSpecificDir string,
	testCase map[*verilog.Port]string,
	sims []*SimInstance,
	simResults map[*SimInstance]map[*verilog.Port]string,
	simErrors map[*SimInstance]error,
	workerModule *verilog.Module,
	testIndex int,
) (bool, error) {
	successfulSimResults := make(map[*SimInstance]map[*verilog.Port]string)
	for simName := range simResults {
		if simErrors[simName] == nil {
			successfulSimResults[simName] = simResults[simName]
		}
	}

	if len(successfulSimResults) < 2 && sch.operation >= OpFuzz {
		sch.debug.Debug(
			"[%s] Test %d: Not enough successful simulator runs (%d) to perform mismatch comparison.",
			workerID,
			testIndex,
			len(successfulSimResults),
		)
		if len(simErrors) > 0 {
			var firstError error
			var firstErrorSim *SimInstance
			for sim, e := range simErrors {
				if e != nil {
					firstError = e
					firstErrorSim = sim
					break
				}
			}
			if firstError != nil {
				return false, fmt.Errorf(
					"only %d sims succeeded, first error from %s: %w",
					len(successfulSimResults),
					firstErrorSim,
					firstError,
				)
			}
		}
		return false, nil
	}

	mismatchFoundThisTest := false

	if sch.operation >= OpFuzz {
		mismatchFoundThisTest, details := sch.compareAllResults(successfulSimResults)

		if mismatchFoundThisTest {
			sch.handleMismatch(
				testIndex,
				testSpecificDir,
				testCase,
				details,
				workerModule,
				sims,
			)
		}
	}

	if len(successfulSimResults) == 0 && len(sims) > 0 {
		var errorMessages []string
		for name, err := range simErrors {
			errorMessages = append(errorMessages, fmt.Sprintf("%s: %v", name, err))
		}
		return false, fmt.Errorf(
			"all simulators failed. Errors: %s",
			strings.Join(errorMessages, "; "),
		)
	}
	return mismatchFoundThisTest, nil
}

func (sch *Scheduler) runSingleTest(
	ctx context.Context,
	workerID, testSpecificDir string,
	sims []*SimInstance,
	workerModule *verilog.Module,
	testIndex int,
	strategy Strategy,
) error {
	// Step 1: Generate Test Case and Prepare Inputs
	testCase, err := sch.generateAndPrepareInputs(
		workerID,
		testSpecificDir,
		workerModule,
		testIndex,
		strategy,
	)
	if err != nil {
		return fmt.Errorf(
			"[%s] Test %d: Failed to generate and prepare inputs: %w",
			workerID,
			testIndex,
			err,
		)
	}

	var mismatchOccurredDuringTest bool
	defer func() {
		if !mismatchOccurredDuringTest && sch.operation >= OpFuzz {
			if sch.verbose <= 2 && !sch.keepFiles {
				os.RemoveAll(testSpecificDir)
			} else {
				sch.debug.Debug("[%s] Test %d: Preserving test directory %s due to verbosity.", workerID, testIndex, testSpecificDir)
			}
		} else if mismatchOccurredDuringTest {
			sch.debug.Info("[%s] Test %d: Preserving test directory %s due to mismatch.", workerID, testIndex, testSpecificDir)
		}
	}()

	sch.debug.Debug("[%s] Test %d: Inputs prepared. Running simulators...", workerID, testIndex)

	// Step 2: Execute Simulators Concurrently
	simResults, simErrors := sch.executeSimulatorsConcurrently(
		ctx,
		workerID,
		testSpecificDir,
		sims,
		workerModule,
		testIndex,
	)

	// Step 3: Detect Mismatches and Handle Them
	mismatchFoundThisTest, errHandlingMismatches := sch.detectAndHandleMismatches(
		workerID,
		testSpecificDir,
		testCase,
		sims,
		simResults,
		simErrors,
		workerModule,
		testIndex,
	)
	if mismatchFoundThisTest {
		mismatchOccurredDuringTest = true
	}

	if errHandlingMismatches != nil {
		// Prefix error messages from detectAndHandleMismatches with context
		return fmt.Errorf("[%s] Test %d: %w", workerID, testIndex, errHandlingMismatches)
	}

	return nil
}

func writeTestInputs(testDir string, testCase map[*verilog.Port]string) error {
	for port, value := range testCase {
		inputPath := filepath.Join(testDir, fmt.Sprintf("input_%s.hex", port.Name))
		if err := os.WriteFile(inputPath, []byte(value), 0o644); err != nil {
			return fmt.Errorf("failed to write input file %s: %v", inputPath, err)
		}
	}
	return nil
}

func (sch *Scheduler) runSimulator(
	ctx context.Context,
	sim simulator.Simulator,
	testSpecificDir string, // e.g., worker_XYZ/test_0
	outputPathsForSim map[*verilog.Port]string, // map portName to final prefixed path in testSpecificDir
) (map[*verilog.Port]string, error) {
	// sim.RunTest expects inputDir (where input_N.hex are) and outputPaths (where to put prefixed_output_N.hex)
	// Both should be relative to testSpecificDir or absolute paths within it.
	if err := sim.RunTest(ctx, testSpecificDir, outputPathsForSim); err != nil {
		return nil, fmt.Errorf("simulator %s RunTest failed: %w", sim.Type(), err)
	}

	if len(outputPathsForSim) > 0 {
		if err := simulator.VerifyOutputFiles(outputPathsForSim); err != nil {
			return nil, fmt.Errorf("output file verification failed for %s: %w", sim.Type(), err)
		}
	}

	results, err := simulator.ReadOutputFiles(outputPathsForSim)
	if err != nil {
		return nil, fmt.Errorf("failed to read output files for %s: %w", sim.Type(), err)
	}
	return results, nil
}
