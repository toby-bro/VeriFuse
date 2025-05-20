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

type Fuzzer struct {
	stats        *Stats
	strategyName string
	workers      int
	verbose      int
	debug        *utils.DebugLogger
	svFile       *verilog.VerilogFile
	mutate       bool
	maxAttempts  int
}

func NewFuzzer(
	strategy string,
	workers int,
	verbose int,
	fileName string,
	mutate bool,
	maxAttempts int,
) *Fuzzer {
	fuzzer := &Fuzzer{
		stats:        NewStats(),
		workers:      workers,
		verbose:      verbose,
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

	if err := simulator.TestIVerilogTool(); err != nil {
		return fmt.Errorf("iverilog tool check failed: %v", err)
	}
	f.debug.Debug("IVerilog tool found.")
	if err := simulator.TestVerilatorTool(); err != nil {
		return fmt.Errorf("verilator tool check failed: %v", err)
	}
	f.debug.Debug("Verilator tool found.")
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
	errChan := make(chan error, max(f.workers, len(f.svFile.Modules)))

	if f.mutate {
		progressTracker := NewProgressTracker(numTests, f.stats, &wg)
		progressTracker.Start()
		defer progressTracker.Stop()
	}
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	workerSlots := make(chan int, f.workers)
	for i := 0; i < f.workers; i++ {
		workerSlots <- i
	}

	f.debug.Debug(
		"Starting %d workers for %d modules so looping %d times",
		f.workers,
		len(f.svFile.Modules),
		f.workers/len(f.svFile.Modules),
	)

	for range max(f.workers/len(f.svFile.Modules), 1) {
		for _, module := range f.svFile.Modules {
			wg.Add(1)
			currentModule := module

			go func(mod *verilog.Module) {
				defer wg.Done()

				slotIdx := <-workerSlots
				defer func() { workerSlots <- slotIdx }()
				f.debug.Info("Worker %d started for module %s", slotIdx, mod.Name)

				if err := f.worker(testCases, mod, slotIdx); err != nil {
					errChan <- fmt.Errorf("worker (slot %d) for module %s error: %w", slotIdx, mod.Name, err)
				}
			}(currentModule)
		}
	}

	f.debug.Debug("Feeding %d test cases to %d workers", numTests, f.workers)

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
		if numTests == 1 {
			f.debug.Info("Successfully fed 1 test case to the channel.")
		} else {
			f.debug.Info("Successfully fed all %d test cases to the channel.", numTests)
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
		f.debug.Error("Fuzzing completed with %d worker error(s):", len(allWorkerErrors))
		for _, we := range allWorkerErrors {
			f.debug.Error("%s", we)
		}
	} else if !f.mutate {
		fmt.Printf("%s[+] File `%s` checked successfully, modules seem valid.%s\n", utils.ColorGreen, f.svFile.Name, utils.ColorReset)
		err := snippets.WriteFileAsSnippets(f.svFile)
		if err != nil {
			return fmt.Errorf("failed to write snippets to file: %v", err)
		}
		f.debug.Info("Snippets written to file successfully.")
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
	if f.mutate {
		f.debug.Info("No mismatches found after %d tests.\n", numTests)
	}
	return nil
}
