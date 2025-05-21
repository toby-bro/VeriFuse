package fuzz

import (
	"context"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"sync"

	"github.com/toby-bro/pfuzz/internal/simulator"
	"github.com/toby-bro/pfuzz/internal/snippets"
	"github.com/toby-bro/pfuzz/internal/verilog"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

type Operation int

const (
	OpFuzz Operation = iota
	OpCheckFile
	OpRewriteValid
)

type Scheduler struct {
	stats            *Stats
	strategyName     string
	workers          int
	verbose          int
	debug            *utils.DebugLogger
	svFile           *verilog.VerilogFile
	operation        Operation
	maxAttempts      int
	cxxrtlIncludeDir string // Added for CXXRTL configuration
}

func NewScheduler(
	strategy string,
	workers int,
	verbose int,
	fileName string,
	operation Operation,
	maxAttempts int,
	cxxrtlIncludeDir string, // Added parameter
) *Scheduler {
	scheduler := &Scheduler{
		stats:            NewStats(),
		workers:          workers,
		verbose:          verbose,
		debug:            utils.NewDebugLogger(verbose),
		operation:        operation,
		maxAttempts:      maxAttempts,
		strategyName:     strategy,
		cxxrtlIncludeDir: cxxrtlIncludeDir, // Store it
	}

	scheduler.svFile = &verilog.VerilogFile{
		Name: fileName,
	}
	return scheduler
}

func (sch *Scheduler) Setup() error {
	if err := utils.EnsureDirs(); err != nil {
		return fmt.Errorf("failed to create directories: %v", err)
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

	if err := utils.CopyFile(fileName, verilogPath); err != nil {
		return fmt.Errorf("failed to copy original Verilog file: %v", err)
	}

	if _, err := os.Stat(verilogPath); os.IsNotExist(err) {
		return fmt.Errorf("copied Verilog file does not exist: %v", err)
	}

	if err := simulator.TestIVerilogTool(); err != nil {
		return fmt.Errorf("iverilog tool check failed: %v", err)
	}
	sch.debug.Debug("IVerilog tool found.")
	if err := simulator.TestVerilatorTool(); err != nil {
		return fmt.Errorf("verilator tool check failed: %v", err)
	}
	if err := simulator.TestCXXRTLTool(); err != nil {
		return fmt.Errorf("cxxrtl tool check failed: %v", err)
	}
	sch.debug.Debug("Verilator tool found.")
	return nil
}

func (sch *Scheduler) Run(numTests int) error {
	sch.debug.Info("Starting fuzzing with %d test cases using strategy: %s",
		numTests, sch.strategyName)
	sch.debug.Info("Target file: %s with %d modules", sch.svFile.Name, len(sch.svFile.Modules))

	if len(sch.svFile.Modules) == 0 {
		return errors.New("no modules found in the provided Verilog file")
	}

	var wg sync.WaitGroup
	testCases := make(chan int, sch.workers)
	errChan := make(chan error, max(sch.workers, len(sch.svFile.Modules)))

	if sch.operation == OpFuzz {
		progressTracker := NewProgressTracker(numTests, sch.stats, &wg)
		progressTracker.Start()
		defer progressTracker.Stop()
	}
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	workerSlots := make(chan int, sch.workers)
	for i := 0; i < sch.workers; i++ {
		workerSlots <- i
	}

	sch.debug.Debug(
		"Starting %d workers for %d modules so looping %d times",
		sch.workers,
		len(sch.svFile.Modules),
		sch.workers/len(sch.svFile.Modules),
	)

	for range max(sch.workers/len(sch.svFile.Modules), 1) {
		for _, module := range sch.svFile.Modules {
			wg.Add(1)
			currentModule := module

			go func(mod *verilog.Module) {
				defer wg.Done()

				slotIdx := <-workerSlots
				defer func() { workerSlots <- slotIdx }()
				sch.debug.Info("Worker %d started for module %s", slotIdx, mod.Name)

				if err := sch.worker(testCases, mod, slotIdx); err != nil {
					errChan <- fmt.Errorf("worker (slot %d) for module %s error: %w", slotIdx, mod.Name, err)
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

		for i := 0; i < numTests; i++ {
			select {
			case testCases <- i:
			case <-ctx.Done():
				sch.debug.Info(
					"Test case feeding cancelled after %d/%d tests (workers finished/terminated or main context cancelled).",
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

	wg.Wait()
	cancel()
	feedingWg.Wait()
	close(errChan)

	var allWorkerErrors []error
	for err := range errChan {
		allWorkerErrors = append(allWorkerErrors, err)
	}
	if len(allWorkerErrors) > 0 {
		sch.debug.Error("Fuzzing completed with %d worker error(s):", len(allWorkerErrors))
		for _, we := range allWorkerErrors {
			sch.debug.Error("%s", we)
		}
	} else {
		switch sch.operation {
		case OpCheckFile:
			fmt.Printf("%s[+] File `%s` checked successfully, modules seem valid.%s\n", utils.ColorGreen, sch.svFile.Name, utils.ColorReset)
		case OpRewriteValid:
			err := snippets.WriteFileAsSnippets(sch.svFile)
			if err != nil {
				sch.debug.Error("failed to write snippets to file: %v", err)
				return fmt.Errorf("failed to write snippets to file: %v", err)
			}
			sch.debug.Info("Snippets written to file successfully.")
		case OpFuzz:
			sch.debug.Info("Fuzzing completed successfully.")
		}
	}

	if sch.operation == OpFuzz {
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

	if sch.stats.Mismatches > 0 && sch.operation == OpFuzz {
		sch.debug.Info("Found %d mismatches between iverilog and verilator!", sch.stats.Mismatches)
		return fmt.Errorf("%d mismatches found", sch.stats.Mismatches)
	}

	if len(allWorkerErrors) > 0 {
		return fmt.Errorf(
			"fuzzing failed due to %d worker errors; first: %w",
			len(allWorkerErrors),
			allWorkerErrors[0],
		)
	}
	if sch.operation == OpFuzz {
		sch.debug.Info("No mismatches found after %d tests.\n", numTests)
	}
	return nil
}
