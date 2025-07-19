package fuzz

import (
	"bytes"
	"context"
	"fmt"
	"math/rand"
	"os"
	"os/exec" // Added for running yosys-config
	"path/filepath"
	"slices"
	"strings"
	"sync"
	"time"

	"github.com/toby-bro/pfuzz/internal/simulator"
	"github.com/toby-bro/pfuzz/internal/snippets"
	"github.com/toby-bro/pfuzz/internal/synth"
	"github.com/toby-bro/pfuzz/pkg/mutate"
	"github.com/toby-bro/pfuzz/pkg/testgen"
	"github.com/toby-bro/pfuzz/pkg/utils"
	"github.com/toby-bro/pfuzz/pkg/verilog"
)

// SimInstance holds a name and a compiled simulator interface.
type SimInstance struct {
	Simulator   simulator.Simulator
	Synthesizer synth.Type
}

func (si *SimInstance) String() string {
	return simulationName(si.Simulator.Type(), si.Synthesizer)
}

func simulationName(sim simulator.Type, synthesizer synth.Type) string {
	if synthesizer == synth.None {
		return sim.String()
	}
	return fmt.Sprintf("%s_%s", sim.String(), synthesizer.String())
}

var logger *utils.DebugLogger

func loadLogger(v int) {
	if logger == nil {
		logger = utils.NewDebugLogger(v)
	}
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

// performWorkerAttempt tries to set up and run tests for one worker attempt.
// It returns true if the setup was successful and test processing started, along with any error from setup.
// If setup was successful, the error returned is nil.
// If setup failed, it returns false and the setup error.
func (sch *Scheduler) performWorkerAttempt(
	ctx context.Context,
	workerID string,
	testCases <-chan int,
	workerModule *verilog.Module,
	strategy Strategy,
	availableSimulators []simulator.Type,
	availableSynthesizers []synth.Type,
) (setupSuccessful bool, err error) {
	workerDir, cleanupFunc, setupErr := sch.setupWorker(workerID)
	if setupErr != nil {
		return false, fmt.Errorf("worker setup failed for %s: %w", workerID, setupErr)
	}

	attemptCompletelySuccessful := false
	defer func() {
		if cleanupFunc != nil {
			if (sch.verbose > 2 && !attemptCompletelySuccessful) || sch.verbose > 3 ||
				sch.keepFiles {
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

	loadLogger(sch.verbose)

	workerVerilogPath := filepath.Join(workerDir, workerModule.Name+".sv")
	var svFile *verilog.VerilogFile
	if sch.operation == OpMutate {
		sch.debug.Debug("[%s] Attempting mutation on %s", workerID, workerVerilogPath)
		if svFile, err = mutate.MutateAndRewriteFile(sch.svFile, workerVerilogPath, sch.verbose); err != nil {
			return false, fmt.Errorf("[%s] mutation failed: %w", workerID, err)
		}
		sch.debug.Debug("[%s] Mutation applied. Proceeding.", workerID)
	} else {
		sch.debug.Debug("[%s] Mutation not requested. Proceeding with original file.", workerID)
		svFile = sch.svFile.DeepCopy()
	}
	svFile.Name = workerModule.Name + ".sv"
	if svFile == sch.svFile {
		logger.Fatal(
			"[%s] svFile is the same as original file. This should not happen.",
			workerID,
		)
	}
	sch.debug.Debug(
		"[%s] Printing minimal file %s for module %s",
		workerID,
		svFile.Name,
		workerModule.Name,
	)
	if err := snippets.PrintMinimalVerilogFileInDist(svFile, workerModule.Name, workerDir); err != nil {
		return false, fmt.Errorf(
			"[%s] failed to print minimal file for module %s in %s: %w",
			workerID,
			workerModule.Name,
			workerDir,
			err,
		)
	}

	for _, synthType := range availableSynthesizers {
		// if sv2v in availableSimulators, transform svFile to Verilog
		switch synthType { //nolint:exhaustive
		case synth.SV2V:
			if err = synth.TransformSV2V(workerModule.Name, workerVerilogPath); err != nil {
				if matches := synth.Sv2vUnexpectedRegex.FindStringSubmatch(err.Error()); len(
					matches,
				) > 0 {
					sch.debug.Info(
						"[%s] sv2v transformation failed for module %s. Unsupported token: `%s`.",
						workerID,
						workerModule.Name,
						matches[1],
					)
				} else {
					sch.debug.Warn(
						"[%s] Failed to transform SystemVerilog to Verilog for module %s: %v",
						workerID,
						workerModule.Name,
						err,
					)
				}
				// delete sv2v from availableSimulators
				availableSynthesizers = slices.DeleteFunc(
					slices.Clone(availableSynthesizers),
					func(t synth.Type) bool {
						return t == synth.SV2V
					},
				)
			}
		case synth.YOSYS:
			if err := synth.YosysSynth(workerModule.Name, workerVerilogPath, nil); err != nil {
				if unsup, pretext := synth.YosysFailedCuzUnsupportedFeature(err); unsup {
					sch.debug.Info(
						"[%s] Yosys synthesis failed for module %s due to unsupported feature: %s",
						workerID,
						workerModule.Name,
						pretext,
					)
				} else {
					sch.debug.Warn(
						"[%s] Yosys synthesis failed for module %s: %v",
						workerID,
						workerModule.Name,
						err,
					)
					// delete yosys from availableSynthesizers
					availableSynthesizers = slices.DeleteFunc(
						slices.Clone(availableSynthesizers),
						func(t synth.Type) bool {
							return t == synth.YOSYS
						},
					)
				}
			} else {
				sch.debug.Debug("[%s] Yosys synthesis successful for module %s", workerID, workerModule.Name)
			}
		case synth.VIVADO:
			if err := synth.VivadoSynthSync(workerModule.Name, workerVerilogPath); err != nil {
				sch.debug.Warn(
					"[%s] Vivado synthesis failed for module %s: %v",
					workerID,
					workerModule.Name,
					err,
				)
				// delete vivado from availableSynthesizers
				availableSynthesizers = slices.DeleteFunc(
					slices.Clone(availableSynthesizers),
					func(t synth.Type) bool {
						return t == synth.VIVADO
					},
				)
			} else {
				sch.debug.Debug("[%s] Vivado synthesis successful for module %s", workerID, workerModule.Name)
			}
		default:
			sch.debug.Warn(
				"[%s] Unsupported synthesizer type %s for module %s",
				workerID,
				synthType,
				workerModule.Name,
			)
		}
	}

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
		"[%s] Generating testbenches for module %s of %s in %s",
		workerID,
		currentWorkerModule.Name,
		svFile.Name,
		workerDir,
	)
	gen := testgen.NewGenerator(
		currentWorkerModule,
		svFile.Name,
		svFile,
	) // Use current (mutated) svFile.Name
	if err := gen.GenerateSVTestbench(workerDir); err != nil { // Generates testbench.sv in workerDir
		return false, fmt.Errorf(
			"[%s] failed to generate SystemVerilog testbenches: %w",
			workerID,
			err,
		)
	}
	if err := gen.GenerateCXXRTLTestbench(workerDir); err != nil { // Pass cxxrtlSimDir
		return false, fmt.Errorf("[%s] failed to generate CXXRTL testbench: %w", workerID, err)
	}

	sch.debug.Debug("[%s] Testbenches generated.", workerID)

	sims, err := sch.setupSimulators(
		ctx,
		workerID,
		workerDir,
		currentWorkerModule,
		svFile,
		availableSimulators,
		availableSynthesizers,
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
		ctx,
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

// compileSimulatorWithTimeout is a helper function that handles compilation with timeout
func (sch *Scheduler) compileSimulatorWithTimeout(
	ctx context.Context,
	workerID string,
	sim simulator.Simulator,
	workDir string,
) error {
	compileCtx, compileCancel := context.WithTimeout(ctx, sch.timeouts.CompilationTimeout)
	defer compileCancel()

	sch.debug.Debug("[%s] Compiling %s simulator in %s", workerID, sim.Type(), workDir)

	if err := sim.Compile(compileCtx); err != nil {
		if unsup, pretext := sim.FailedCuzUnsupportedFeature(err); unsup {
			sch.debug.Info(
				"[%s] %s compilation failed due to unsupported feature: %v",
				workerID,
				sim.Type(),
				pretext,
			)
		} else {
			sch.debug.Warn("[%s] Failed to compile %s: %v", workerID, sim.Type(), err)
		}
		return fmt.Errorf("%s: %v", sim.Type(), err)
	}

	sch.debug.Debug("[%s] %s compiled successfully.", workerID, sim.Type())
	return nil
}

var (
	cxxrtlIncludeDir     string
	cxxrtlIncludeDirOnce sync.Once
)

// getCXXRTLIncludeDir determines the CXXRTL include directory using yosys-config.
// It runs only once and caches the result for subsequent calls.
func (sch *Scheduler) getCXXRTLIncludeDir() string {
	cxxrtlIncludeDirOnce.Do(func() {
		yosysCmd := exec.Command("yosys-config", "--datdir")
		var yosysOut bytes.Buffer
		var yosysErr bytes.Buffer
		yosysCmd.Stdout = &yosysOut
		yosysCmd.Stderr = &yosysErr

		if err := yosysCmd.Run(); err == nil {
			yosysDatDir := strings.TrimSpace(yosysOut.String())
			potentialPath := filepath.Join(
				yosysDatDir,
				"include",
				"backends",
				"cxxrtl",
				"runtime",
			)

			if _, err := os.Stat(potentialPath); err == nil {
				sch.debug.Debug(
					"Using CXXRTL_INCLUDE_DIR (runtime) from yosys-config: %s",
					potentialPath,
				)
				cxxrtlIncludeDir = potentialPath
				return
			}
			sch.debug.Debug(
				"yosys-config derived CXXRTL runtime path %s not found (stat error: %v). Will try defaults.",
				potentialPath,
				err,
			)
		} else {
			errMsg := strings.TrimSpace(yosysErr.String())
			sch.debug.Warn("'yosys-config --datdir' command failed: %v. Stderr: '%s'. Will try default CXXRTL include paths.", err, errMsg)
		}
		cxxrtlIncludeDir = ""
	})
	return cxxrtlIncludeDir
}

func (sch *Scheduler) setupSimulator(
	ctx context.Context,
	simType simulator.Type,
	workerID string,
	baseWorkerDir string,
	svFile *verilog.VerilogFile,
	workerModule *verilog.Module,
	synthType synth.Type,
) (*SimInstance, error) {
	workDir := filepath.Join(baseWorkerDir, simulationName(simType, synthType))
	if err := os.MkdirAll(workDir, 0o755); err != nil {
		return nil, fmt.Errorf("%s_mkdir: %v", simulationName(simType, synthType), err)
	}
	sim := simType.SetupSimulator(
		workDir,
		svFile,
		workerModule,
		sch.verbose,
		sch.getCXXRTLIncludeDir(),
	)

	if sim == nil {
		return nil, fmt.Errorf(
			"[%s] setupSimulator: %s simulator is not supported or not found",
			workerID,
			simType.String(),
		)
	}

	if err := sch.compileSimulatorWithTimeout(
		ctx,
		workerID,
		sim,
		workDir,
	); err != nil {
		return nil, fmt.Errorf(
			"[%s] setupSimulator: failed to compile %s simulator: %v",
			workerID,
			simType.String(),
			err,
		)
	}
	return &SimInstance{
		Simulator:   sim,
		Synthesizer: synthType,
	}, nil
}

func (sch *Scheduler) setupSimulators(
	ctx context.Context,
	workerID string, baseWorkerDir string, workerModule *verilog.Module,
	svFileToCompile *verilog.VerilogFile,
	availableSimulators []simulator.Type,
	availableSynthesizers []synth.Type,
) ([]*SimInstance, error) {
	sch.debug.Debug(
		"[%s] Setting up simulators for module %s in %s",
		workerID,
		workerModule.Name,
		baseWorkerDir,
	)
	var compiledSims []*SimInstance
	var setupErrors []string

	// Setup each simulator
	for _, sim := range availableSimulators {
		if simInstance, err := sch.setupSimulator(ctx, sim, workerID, baseWorkerDir, svFileToCompile, workerModule, synth.None); err != nil {
			setupErrors = append(setupErrors, err.Error())
		} else {
			compiledSims = append(compiledSims, simInstance)
		}
	}

	// Setup synthesizer variants
	for _, synthType := range availableSynthesizers {
		sch.setupSynthVariants(
			ctx,
			workerID,
			baseWorkerDir,
			workerModule,
			svFileToCompile,
			synthType,
			availableSimulators,
			&compiledSims,
			&setupErrors,
		)
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

// setupSynthVariants sets up synthesizer variants based on file extension and suffix
func (sch *Scheduler) setupSynthVariants(
	ctx context.Context,
	workerID string,
	baseWorkerDir string,
	workerModule *verilog.Module,
	svFileToCompile *verilog.VerilogFile,
	synthType synth.Type,
	availableSimulators []simulator.Type,
	compiledSims *[]*SimInstance,
	setupErrors *[]string,
) {
	synthFileName := utils.ChangeExtension(svFileToCompile.Name, "v")
	synthFileName = utils.AddSuffixToPath(synthFileName, synthType.String())
	synthFilePath := filepath.Join(baseWorkerDir, synthFileName)

	// Check if the synthesized file exists
	if !utils.FileExists(synthFilePath) {
		synthFileName = utils.ChangeExtension(svFileToCompile.Name, "sv")
		synthFilePath = filepath.Join(baseWorkerDir, synthFileName)
		if !utils.FileExists(filepath.Join(baseWorkerDir, synthFileName)) {
			sch.debug.Error(
				"[%s] No .v or .sv file found at %s, skipping %s simulator variants",
				workerID,
				synthFilePath,
				synthType.String(),
			)
			return
		}
	}

	sch.debug.Debug(
		"[%s] Found .v file at %s, creating %s simulator variants",
		workerID,
		synthFilePath,
		synthType.String(),
	)

	var synthFile *verilog.VerilogFile
	var err error

	// For non-SystemVerilog files, parse and create VerilogFile object
	synthFileContent, readErr := os.ReadFile(synthFilePath)
	if readErr != nil {
		sch.debug.Error(
			"[%s] Failed to read .v file %s: %v",
			workerID,
			synthFilePath,
			readErr,
		)
		return
	}

	synthFile, err = verilog.ParseVerilog(string(synthFileContent), sch.verbose)
	if err != nil {
		sch.debug.Error(
			"[%s] Failed to parse .v file %s: %v",
			workerID,
			synthFilePath,
			err,
		)
		return
	}
	synthFile.Name = synthFileName

	availableSimulators = slices.DeleteFunc(
		slices.Clone(availableSimulators),
		func(t simulator.Type) bool {
			return t == simulator.XCELIUM
		},
	)

	// Randomly select one synthesizer variant
	selectedVariant := availableSimulators[rand.Intn(len(availableSimulators))]
	if simInstance, err := sch.setupSimulator(ctx, selectedVariant, workerID, baseWorkerDir, svFileToCompile, workerModule, synthType); err != nil {
		*setupErrors = append(*setupErrors, err.Error())
	} else {
		*compiledSims = append(*compiledSims, simInstance)
	}
}

func (sch *Scheduler) worker(
	ctx context.Context,
	testCases <-chan int,
	moduleToTest *verilog.Module,
	workerNum int,
	availableSimulators []simulator.Type,
	availableSynthesizers []synth.Type,
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
			ctx,
			workerCompleteID,
			testCases,
			moduleToTest,
			strategy,
			availableSimulators,
			availableSynthesizers,
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
