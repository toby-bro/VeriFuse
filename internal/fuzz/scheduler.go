package fuzz

import (
	"context"
	"errors"
	"fmt"
	"path/filepath"
	"runtime"
	"sync"
	"time"

	"github.com/toby-bro/pfuzz/internal/simulator"
	"github.com/toby-bro/pfuzz/internal/snippets"
	"github.com/toby-bro/pfuzz/internal/synth"
	"github.com/toby-bro/pfuzz/pkg/utils"
	"github.com/toby-bro/pfuzz/pkg/verilog"
)

type Operation int

const (
	OpCheckFile Operation = iota
	OpRewriteValid
	OpFuzz
	OpMutate
)

// TimeoutConfig holds timeout configurations for different operations
type TimeoutConfig struct {
	CompilationTimeout time.Duration // Timeout for simulator compilation
	TestTimeout        time.Duration // Timeout for individual test execution
	OverallTimeout     time.Duration // Overall timeout for the entire fuzzing session
}

// DefaultTimeoutConfig returns sensible default timeout values
func DefaultTimeoutConfig() TimeoutConfig {
	return TimeoutConfig{
		CompilationTimeout: 30 * time.Second,
		TestTimeout:        30 * time.Second,
		OverallTimeout:     5 * time.Minute,
	}
}

type Scheduler struct {
	stats        *Stats
	strategyName string
	workers      int
	verbose      int
	debug        *utils.DebugLogger
	svFile       *verilog.VerilogFile
	operation    Operation
	maxAttempts  int
	keepFiles    bool
	timeouts     TimeoutConfig
}

func NewScheduler(
	strategy string,
	workers int,
	verbose int,
	fileName string,
	operation Operation,
	maxAttempts int,
	keepFiles bool,
) *Scheduler {
	scheduler := &Scheduler{
		stats:        NewStats(),
		workers:      workers,
		verbose:      verbose,
		debug:        utils.NewDebugLogger(verbose),
		operation:    operation,
		maxAttempts:  maxAttempts,
		strategyName: strategy,
		keepFiles:    keepFiles,
		timeouts:     DefaultTimeoutConfig(),
	}

	scheduler.svFile = &verilog.VerilogFile{
		Name: fileName,
	}
	return scheduler
}

func (sch *Scheduler) Setup() ([]simulator.Type, []synth.Type, error) {
	if err := utils.EnsureDirs(); err != nil {
		return nil, nil, fmt.Errorf("failed to create directories: %v", err)
	}

	fileName := sch.svFile.Name

	fileContent, err := utils.ReadFileContent(fileName)
	if err != nil {
		sch.debug.Fatal("Failed to read file %s: %v", fileName, err)
	}
	sch.svFile, err = verilog.ParseVerilog(fileContent, sch.verbose)
	if err != nil {
		sch.debug.Fatal("Failed to parse file %s: %v", fileName, err)
	}
	sch.svFile.Name = filepath.Base(fileName)

	verilogPath := filepath.Join(utils.TMP_DIR, filepath.Base(fileName))
	sch.debug.Debug("Copying original Verilog file `%s` to `%s`", fileName, verilogPath)

	availableSimulators := simulator.TestAvailableSimulators(sch.debug)
	sch.debug.Info(
		"Found %d available simulators: %v",
		len(availableSimulators),
		availableSimulators,
	)

	availableSynthesizers := synth.TestAvailableSynthesizers(sch.debug)
	sch.debug.Info(
		"Found %d available synthesizers: %v",
		len(availableSynthesizers),
		availableSynthesizers,
	)

	if len(availableSimulators) < 2 {
		return nil, nil, fmt.Errorf(
			"at least two simulators are required for fuzzing, but only found %d: %v",
			len(availableSimulators),
			availableSimulators,
		)
	}
	return availableSimulators, availableSynthesizers, nil
}

type workerError struct {
	module *verilog.Module
	err    error
}

func dumpAllWorkerErrors(
	allWorkerErrors map[*verilog.Module]error,
	debug *utils.DebugLogger,
	operation string,
) {
	if len(allWorkerErrors) > 0 {
		debug.Error("%s completed with %d worker error(s):", operation, len(allWorkerErrors))
		for module, we := range allWorkerErrors {
			debug.Error("Module %s: %s", module.Name, we)
		}
	} else {
		debug.Info("%s completed successfully with no worker errors.", operation)
	}
}

func (sch *Scheduler) Run(
	numTests int,
	availableSimulators []simulator.Type,
	availableSynthesizers []synth.Type,
) error {
	sch.debug.Info("Starting fuzzing with %d test cases using strategy: %s",
		numTests, sch.strategyName)
	sch.debug.Info("Target file: %s with %d modules", sch.svFile.Name, len(sch.svFile.Modules))

	if len(sch.svFile.Modules) == 0 {
		return errors.New("no modules found in the provided Verilog file")
	}

	var wg sync.WaitGroup
	testCases := make(chan int, sch.workers)

	errChan := make(chan workerError, max(sch.workers, len(sch.svFile.Modules)))

	// Create main context with overall timeout
	ctx, cancel := context.WithTimeout(context.Background(), sch.timeouts.OverallTimeout)
	defer cancel()

	sch.debug.Info("Fuzzing session timeout set to %v", sch.timeouts.OverallTimeout)

	// CPU-bound execution slots to prevent system overload
	numCPUs := runtime.NumCPU()
	cpuSlots := make(chan struct{}, numCPUs)
	for i := 0; i < numCPUs; i++ {
		cpuSlots <- struct{}{}
	}

	workerSlots := make(chan int, sch.workers)
	for i := 0; i < sch.workers; i++ {
		workerSlots <- i
	}

	sch.debug.Info("Using %d CPU cores for concurrent execution limiting", numCPUs)

	sch.debug.Debug(
		"Starting %d workers for %d modules so looping %d times",
		sch.workers,
		len(sch.svFile.Modules),
		sch.workers/len(sch.svFile.Modules),
	)

	workerLoopCount := max(sch.workers/len(sch.svFile.Modules), 1)
	for range workerLoopCount {
		for _, module := range sch.svFile.Modules {
			wg.Add(1)
			currentModule := module

			go func(mod *verilog.Module) {
				defer wg.Done()

				slotIdx := <-workerSlots
				defer func() { workerSlots <- slotIdx }()
				sch.debug.Info("Worker %d started for module %s", slotIdx, mod.Name)

				<-cpuSlots
				defer func() { cpuSlots <- struct{}{} }()

				if err := sch.worker(ctx, testCases, mod, slotIdx, availableSimulators, availableSynthesizers); err != nil {
					errChan <- workerError{module: mod, err: fmt.Errorf("[worker_%d] for module %s error: \n[-] ERROR: %w", slotIdx, mod.Name, err)}
				}
			}(currentModule)
		}
	}

	sch.debug.Debug("Feeding %d test cases to %d workers", numTests, sch.workers)

	var feedingWg sync.WaitGroup
	feedingWg.Add(1)
	go func() {
		defer feedingWg.Done()
		defer close(testCases)

		for i := workerLoopCount - 1; i < numTests; i++ {
			select {
			case testCases <- i:
			case <-ctx.Done():
				sch.debug.Info(
					"Scheduler: Test case feeding cancelled after %d/%d tests (workers finished/terminated or main context cancelled).",
					i,
					numTests,
				)
				return
			}
		}
		if numTests == 1 {
			sch.debug.Info("Successfully fed 1 test case to the channel.")
		} else {
			sch.debug.Info("Successfully fed all %d test cases to the channel.", numTests)
		}
	}()

	if sch.operation >= OpFuzz {
		progressTracker := NewProgressTracker(numTests, sch.stats, &wg)
		progressTracker.Start()
		defer progressTracker.Stop()
	}

	wg.Wait()
	cancel()
	feedingWg.Wait()
	close(errChan)

	allWorkerErrors := make(map[*verilog.Module]error)
	for workerErr := range errChan {
		allWorkerErrors[workerErr.module] = workerErr.err
	}
	switch sch.operation {
	case OpFuzz, OpMutate:
		dumpAllWorkerErrors(allWorkerErrors, sch.debug, "Fuzzing")
	case OpCheckFile:
		dumpAllWorkerErrors(allWorkerErrors, sch.debug, "File Check")
	case OpRewriteValid:
		var validModules []*verilog.Module
		for _, mod := range sch.svFile.Modules {
			if _, failed := allWorkerErrors[mod]; !failed {
				validModules = append(validModules, mod)
			}
		}
		if len(validModules) > 0 {
			err := snippets.WriteFileAsSnippetsSubset(sch.svFile, validModules)
			if err != nil {
				sch.debug.Error("failed to write snippets to file: %v", err)
				return fmt.Errorf("failed to write snippets to file: %v", err)
			}
			sch.debug.Info("Snippets written to file successfully for valid modules.")
		}
		dumpAllWorkerErrors(allWorkerErrors, sch.debug, "Rewrite Valid")
	}

	if sch.operation >= OpFuzz {
		sch.stats.PrintSummary()
	}

	if numTests > 0 && sch.stats.TotalTests == 0 {
		sch.debug.Warn("Fuzzing completed, but no test cases were successfully executed.")
		sch.debug.Warn(
			"Out of %d test cases requested, %d were run.",
			numTests,
			sch.stats.TotalTests,
		)
		sch.debug.Warn(
			"This often indicates a persistent problem in the test case generation or worker setup phase for all workers.",
		)
		sch.debug.Warn(
			"Common causes include: missing resources required by the fuzzing strategy, or other strategy-specific initialization failures leading to simulator compilation errors.",
		)
		sch.debug.Warn("Please review logs for worker-specific error messages.")
		return fmt.Errorf(
			"fuzzing finished but no tests were executed out of %d requested; check logs for worker setup or test generation errors",
			numTests,
		)
	}

	if sch.stats.Mismatches > 0 && sch.operation >= OpFuzz {
		sch.debug.Info("Found %d mismatches !", sch.stats.Mismatches)
		return fmt.Errorf("%d mismatches found", sch.stats.Mismatches)
	}

	if sch.operation >= OpFuzz {
		sch.debug.Info("No mismatches found after %d tests.\n", numTests)
	}
	return nil
}
