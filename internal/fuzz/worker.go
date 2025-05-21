package fuzz

import (
	"fmt"
	"os"
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
	CX_PREFIX = "cx_" // Prefix for CXXRTL
)

// SimInstance holds a name and a compiled simulator interface.
type SimInstance struct {
	Name      string
	Simulator simulator.Simulator
}

func (sch *Scheduler) setupWorker(workerID string) (string, func(), error) {
	workerDir := filepath.Join(utils.TMP_DIR, workerID)
	sch.debug.Debug("[%s] Creating worker directory at %s", workerID, workerDir)
	if err := os.MkdirAll(workerDir, 0o755); err != nil {
		sch.debug.Error("[%s] Failed to create worker directory %s: %v", workerID, workerDir, err)
		return "", nil, err
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
		if err != nil {
			return false, fmt.Errorf("[%s] failed to parse Verilog file: %w", workerID, err)
		}
		svFile.Name = sch.svFile.Name // Ensure basename is correct
	}

	// svFile now represents the Verilog content for this attempt, located at workerVerilogPath.
	// Its svFile.Name is the base name (e.g., "design.v").

	if err != nil { // This check seems redundant now as errors are handled above.
		return false, fmt.Errorf(
			"[%s] failed to parse (potentially mutated) Verilog: %w",
			workerID,
			err,
		)
	}
	sch.debug.Debug(
		"[%s] Parsed %d modules from file %s (path: %s).",
		workerID,
		len(svFile.Modules),
		svFile.Name,
		workerVerilogPath,
	)

	// Ensure workerModule is from the current svFile
	currentWorkerModule, ok := svFile.Modules[workerModule.Name]
	if !ok {
		return false, fmt.Errorf(
			"[%s] worker module %s not found in parsed file %s for current attempt",
			workerID,
			workerModule.Name,
			svFile.Name,
		)
	}

	sch.debug.Debug(
		"[%s] Generating testbenches for module %s in %s",
		workerID,
		currentWorkerModule.Name,
		workerDir,
	)
	gen := testgen.NewGenerator(
		currentWorkerModule,
		svFile.Name,
	) // Use current (mutated) svFile.Name
	if err := gen.GenerateSVTestbench(workerDir); err != nil { // Generates testbench.sv in workerDir
		return false, fmt.Errorf(
			"[%s] failed to generate SystemVerilog testbenches: %w",
			workerID,
			err,
		)
	}

	// Check if CXXRTL is intended to be used and generate its testbench
	cxxrtlSimDir := filepath.Join(workerDir, "cxxrtl_sim")
	if err := os.MkdirAll(cxxrtlSimDir, 0o755); err != nil {
		return false, fmt.Errorf("[%s] failed to create cxxrtl_sim dir: %w", workerID, err)
	}
	if err := gen.GenerateCXXRTLTestbench(cxxrtlSimDir); err != nil { // Pass cxxrtlSimDir
		return false, fmt.Errorf("[%s] failed to generate CXXRTL testbench: %w", workerID, err)
	}
	sch.debug.Debug("[%s] Testbenches generated.", workerID)

	sims, err := sch.setupSimulators(
		workerID,
		workerDir,
		currentWorkerModule.Name,
		svFile,
	) // Pass current svFile
	if err != nil {
		// If setupSimulators returns an error, it means no simulators could be compiled.
		// Specific compilation errors for individual simulators are logged within setupSimulators.
		// We might want to call handleGenericCompilationFailure here if *all* fail.
		return false, fmt.Errorf("simulator setup failed for worker %s: %w", workerID, err)
	}

	sch.debug.Debug(
		"[%s] Simulators set up successfully: %d simulators ready.",
		workerID,
		len(sims),
	)
	sch.debug.Debug(
		"[%s] Starting test case processing for module %s. Strategy: %s",
		workerID,
		currentWorkerModule.Name,
		strategy.Name(),
	)

	errorList := sch.processTestCases(
		workerID,
		workerDir, // This is the base directory for the worker attempt
		sims,      // Pass the slice of SimInstance
		currentWorkerModule,
		testCases,
		strategy,
	)
	if len(errorList) > 0 {
		var errBuilder strings.Builder
		for i, e := range errorList {
			if i > 0 {
				errBuilder.WriteString("; ")
			}
			errBuilder.WriteString(e.Error())
		}
		return false, fmt.Errorf(
			"[%s] test case processing failed with %d errors: %s",
			workerID,
			len(errorList),
			errBuilder.String(),
		)
	}
	attemptCompletelySuccessful = true // Mark as successful for cleanup logic
	return true, nil
}

func (sch *Scheduler) setupSimulators(
	workerID, baseWorkerDir, workerModuleName string,
	svFileToCompile *verilog.VerilogFile, // svFileToCompile is the (potentially mutated) one
) ([]*SimInstance, error) {
	sch.debug.Debug(
		"[%s] Setting up simulators for module %s in %s",
		workerID,
		workerModuleName,
		baseWorkerDir,
	)
	var compiledSims []*SimInstance
	var setupErrors []string

	// 1. Icarus Verilog
	ivWorkDir := baseWorkerDir // Icarus compiles in the base worker dir
	ivsim := simulator.NewIVerilogSimulator(ivWorkDir, sch.verbose)
	sch.debug.Debug("[%s] Compiling IVerilog simulator in %s", workerID, ivWorkDir)
	if err := ivsim.Compile(); err != nil {
		sch.debug.Warn("[%s] Failed to compile IVerilog: %v", workerID, err)
		setupErrors = append(setupErrors, fmt.Sprintf("iverilog: %v", err))
		// sch.handleGenericCompilationFailure(workerID, workerModuleName, "iverilog", err, baseWorkerDir)
	} else {
		sch.debug.Debug("[%s] IVerilog compiled successfully.", workerID)
		compiledSims = append(compiledSims, &SimInstance{Name: "iverilog", Simulator: ivsim})
	}

	// 2. Verilator O0
	vlO0WorkDir := filepath.Join(baseWorkerDir, "vl_O0")
	if err := os.MkdirAll(vlO0WorkDir, 0o755); err != nil {
		sch.debug.Warn(
			"[%s] Failed to create Verilator O0 directory %s: %v",
			workerID,
			vlO0WorkDir,
			err,
		)
		setupErrors = append(setupErrors, fmt.Sprintf("verilator_O0_mkdir: %v", err))
	} else {
		vlsim0 := simulator.NewVerilatorSimulator(vlO0WorkDir, svFileToCompile, workerModuleName, false, sch.verbose)
		sch.debug.Debug("[%s] Compiling Verilator O0 simulator in %s", workerID, vlO0WorkDir)
		if err := vlsim0.Compile(); err != nil {
			sch.debug.Warn("[%s] Failed to compile Verilator O0: %v", workerID, err)
			setupErrors = append(setupErrors, fmt.Sprintf("verilator_O0: %v", err))
			// sch.handleGenericCompilationFailure(workerID, workerModuleName, "verilator_O0", err, baseWorkerDir)
		} else {
			sch.debug.Debug("[%s] Verilator O0 compiled successfully.", workerID)
			compiledSims = append(compiledSims, &SimInstance{Name: "verilator_O0", Simulator: vlsim0})
		}
	}

	// 3. Verilator O3
	vlO3WorkDir := filepath.Join(baseWorkerDir, "vl_O3")
	if err := os.MkdirAll(vlO3WorkDir, 0o755); err != nil {
		sch.debug.Warn(
			"[%s] Failed to create Verilator O3 directory %s: %v",
			workerID,
			vlO3WorkDir,
			err,
		)
		setupErrors = append(setupErrors, fmt.Sprintf("verilator_O3_mkdir: %v", err))
	} else {
		vlsim3 := simulator.NewVerilatorSimulator(vlO3WorkDir, svFileToCompile, workerModuleName, true, sch.verbose)
		sch.debug.Debug("[%s] Compiling Verilator O3 simulator in %s", workerID, vlO3WorkDir)
		if err := vlsim3.Compile(); err != nil {
			sch.debug.Warn("[%s] Failed to compile Verilator O3: %v", workerID, err)
			setupErrors = append(setupErrors, fmt.Sprintf("verilator_O3: %v", err))
			// sch.handleGenericCompilationFailure(workerID, workerModuleName, "verilator_O3", err, baseWorkerDir)
		} else {
			sch.debug.Debug("[%s] Verilator O3 compiled successfully.", workerID)
			compiledSims = append(compiledSims, &SimInstance{Name: "verilator_O3", Simulator: vlsim3})
		}
	}

	// 4. CXXRTL
	cxxrtlWorkDir := filepath.Join(
		baseWorkerDir,
		"cxxrtl_sim",
	) // Matches dir used for testbench generation
	// Ensure CXXRTL include directory is available from scheduler config
	includeDir := sch.cxxrtlIncludeDir
	if includeDir == "" {
		// Attempt to find it or use a common default, warn if not found.
		defaultPath := "/usr/local/share/cxxrtl/include"
		if _, err := os.Stat(defaultPath); !os.IsNotExist(err) {
			includeDir = defaultPath
		} else {
			defaultPath = "/usr/share/cxxrtl/include" // Another common path
			if _, err2 := os.Stat(defaultPath); !os.IsNotExist(err2) {
				includeDir = defaultPath
			}
		}
		if includeDir == "" {
			sch.debug.Error(
				"[%s] CXXRTL_INCLUDE_DIR is not configured and common defaults not found. CXXRTL will likely fail.",
				workerID,
			)
			// Do not skip compilation, let it try and fail to capture the error.
		} else {
			sch.debug.Debug("[%s] Using CXXRTL_INCLUDE_DIR: %s", workerID, includeDir)
		}
	}
	// svFileToCompile.Name is the base name of the Verilog file (e.g., design.v)
	cxxrtlOriginalVerilogBaseName := svFileToCompile.Name
	cxsim := simulator.NewCXXRTLSimulator(
		cxxrtlWorkDir,
		cxxrtlOriginalVerilogBaseName,
		workerModuleName,
		includeDir,
		false,
		sch.verbose,
	)
	sch.debug.Debug("[%s] Compiling CXXRTL simulator in %s", workerID, cxxrtlWorkDir)
	if err := cxsim.Compile(); err != nil {
		sch.debug.Warn("[%s] Failed to compile CXXRTL: %v", workerID, err)
		setupErrors = append(setupErrors, fmt.Sprintf("cxxrtl: %v", err))
		// sch.handleGenericCompilationFailure(workerID, workerModuleName, "cxxrtl", err, baseWorkerDir)
	} else {
		sch.debug.Debug("[%s] CXXRTL compiled successfully.", workerID)
		compiledSims = append(compiledSims, &SimInstance{Name: "cxxrtl", Simulator: cxsim})
	}

	if len(compiledSims) == 0 {
		return nil, fmt.Errorf(
			"[%s] no simulators compiled successfully. Errors: %s",
			workerID,
			strings.Join(setupErrors, "; "),
		)
	}

	sch.debug.Info("[%s] Successfully compiled %d simulators.", workerID, len(compiledSims))
	return compiledSims, nil
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
	sims []*SimInstance, // Changed from ivsim, vlsim
	workerModule *verilog.Module,
	testCases <-chan int,
	strategy Strategy,
) []error {
	var errorCollector []error
	var errorMu sync.Mutex

	for i := range testCases {
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
			errorCollector = append(errorCollector, err)
			errorMu.Unlock()
			continue
		}

		err := sch.runSingleTest(workerID, testSpecificDir, sims, workerModule, i, strategy)
		if err != nil {
			sch.debug.Error("[%s] Test %d failed: %v", workerID, i, err)
			errorMu.Lock()
			errorCollector = append(errorCollector, err)
			errorMu.Unlock()
		}
	}
	return errorCollector
}

func (sch *Scheduler) runSingleTest(
	workerID, testSpecificDir string,
	sims []*SimInstance, // Changed from ivsim, vlsim
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

	if err := writeTestInputs(testSpecificDir, testCase); err != nil {
		return fmt.Errorf("[%s] Test %d: Failed to write inputs: %w", workerID, testIndex, err)
	}

	mismatchOccurred := false
	defer func() {
		if !mismatchOccurred && sch.operation == OpFuzz {
			if sch.verbose <= 2 { // Keep if verbose enough
				os.RemoveAll(testSpecificDir)
			} else {
				sch.debug.Debug("[%s] Test %d: Preserving test directory %s due to verbosity.", workerID, testIndex, testSpecificDir)
			}
		} else if mismatchOccurred {
			sch.debug.Info("[%s] Test %d: Preserving test directory %s due to mismatch.", workerID, testIndex, testSpecificDir)
		}
	}()

	simResults := make(map[string]map[string]string) // simName -> {portName -> value}
	simErrors := make(map[string]error)              // simName -> error
	var resultsMu sync.Mutex
	var wg sync.WaitGroup

	for _, simInstance := range sims {
		wg.Add(1)
		go func(si *SimInstance) {
			defer wg.Done()
			sch.debug.Debug("[%s] Test %d: Running simulator %s", workerID, testIndex, si.Name)

			currentSimOutputPaths := make(map[string]string)
			for _, port := range workerModule.Ports {
				if port.Direction == verilog.OUTPUT {
					var prefix string
					switch si.Name {
					case "iverilog":
						prefix = IV_PREFIX
					case "verilator_O0", "verilator_O3":
						prefix = VL_PREFIX
					case "cxxrtl":
						prefix = CX_PREFIX
					default:
						// Ensure the slice is safe and handle potential empty name
						if len(si.Name) > 0 {
							prefix = strings.ToLower(si.Name[:min(3, len(si.Name))]) + "_"
						} else {
							prefix = "unk_" // Fallback for empty simulator name
						}
					}
					outputFile := fmt.Sprintf("%s%s.hex", prefix, port.Name)
					currentSimOutputPaths[port.Name] = filepath.Join(testSpecificDir, outputFile)
				}
			}

			results, err := sch.runSimulator(
				si.Name,
				si.Simulator,
				testSpecificDir,
				currentSimOutputPaths,
				workerModule,
			)
			resultsMu.Lock()
			if err != nil {
				simErrors[si.Name] = err
				sch.debug.Error(
					"[%s] Test %d: Simulator %s failed: %v",
					workerID,
					testIndex,
					si.Name,
					err,
				)
			} else {
				simResults[si.Name] = results
				sch.debug.Debug("[%s] Test %d: Simulator %s completed.", workerID, testIndex, si.Name)
			}
			resultsMu.Unlock()
		}(simInstance)
	}
	wg.Wait()

	// --- Mismatch Detection and Handling ---
	successfulSimNames := []string{}
	for simName := range simResults {
		if simErrors[simName] == nil {
			successfulSimNames = append(successfulSimNames, simName)
		}
	}

	if len(successfulSimNames) < 2 && sch.operation == OpFuzz {
		sch.debug.Debug(
			"[%s] Test %d: Not enough successful simulator runs (%d) to perform mismatch comparison.",
			workerID,
			testIndex,
			len(successfulSimNames),
		)
		// If only one (or zero) sim succeeded, check if any sim at all failed.
		if len(simErrors) > 0 {
			var firstError error
			var firstErrorSimName string
			for name, e := range simErrors {
				if e != nil {
					firstError = e
					firstErrorSimName = name
					break
				}
			}
			if firstError != nil {
				return fmt.Errorf(
					"[%s] Test %d: Only %d sims succeeded, first error from %s: %w",
					workerID,
					testIndex,
					len(successfulSimNames),
					firstErrorSimName,
					firstError,
				)
			}
		}
		return nil // Not enough to compare, but no explicit error to return for the test itself unless all failed.
	}

	if sch.operation == OpFuzz {
		var referenceSimName string
		// Prefer Icarus as reference
		for _, name := range successfulSimNames {
			if name == "iverilog" {
				referenceSimName = name
				break
			}
		}
		if referenceSimName == "" && len(successfulSimNames) > 0 {
			referenceSimName = successfulSimNames[0] // Fallback to the first successful one
		}

		if referenceSimName != "" {
			referenceResults := simResults[referenceSimName]
			for _, currentSimName := range successfulSimNames {
				if currentSimName == referenceSimName {
					continue
				}
				currentResults := simResults[currentSimName]
				mismatchFoundThisPair, details := sch.comparePairResults(
					referenceResults,
					currentResults,
					referenceSimName,
					currentSimName,
				)
				if mismatchFoundThisPair {
					mismatchOccurred = true
					sch.handleMismatch(
						testIndex,
						testSpecificDir,
						testCase,
						details,
						workerModule,
						referenceSimName, // Pass sim names
						currentSimName,
					)
					// sch.stats.AddMismatch(testCase) // Moved to handleMismatch
					break // Report first mismatch pair and stop for this test case
				}
			}
		} else if len(successfulSimNames) > 0 {
			// This case should ideally not be hit if the above logic is correct
			sch.debug.Warn("[%s] Test %d: Have successful sims but no reference sim selected.", workerID, testIndex)
		}
	}

	// Check if ALL simulators failed
	if len(successfulSimNames) == 0 && len(sims) > 0 {
		var errorMessages []string
		for name, err := range simErrors {
			errorMessages = append(errorMessages, fmt.Sprintf("%s: %v", name, err))
		}
		return fmt.Errorf(
			"[%s] Test %d: All simulators failed. Errors: %s",
			workerID,
			testIndex,
			strings.Join(errorMessages, "; "),
		)
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
	testSpecificDir string, // e.g., worker_XYZ/test_0
	outputPathsForSim map[string]string, // map portName to final prefixed path in testSpecificDir
	module *verilog.Module,
) (map[string]string, error) {
	// sim.RunTest expects inputDir (where input_N.hex are) and outputPaths (where to put prefixed_output_N.hex)
	// Both should be relative to testSpecificDir or absolute paths within it.
	if err := sim.RunTest(testSpecificDir, outputPathsForSim); err != nil {
		return nil, fmt.Errorf("simulator %s RunTest failed: %w", simName, err)
	}

	if len(outputPathsForSim) > 0 {
		if err := simulator.VerifyOutputFiles(outputPathsForSim); err != nil {
			return nil, fmt.Errorf("output file verification failed for %s: %w", simName, err)
		}
	}

	results, err := simulator.ReadOutputFiles(outputPathsForSim)
	if err != nil {
		return nil, fmt.Errorf("failed to read output files for %s: %w", simName, err)
	}
	return results, nil
}
