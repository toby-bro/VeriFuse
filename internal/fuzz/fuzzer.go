package fuzz

import (
	"context"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"sync"

	"github.com/toby-bro/pfuzz/internal/simulator"
	"github.com/toby-bro/pfuzz/internal/verilog"
	"github.com/toby-bro/pfuzz/pkg/utils"
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
			if err := f.worker(testCases, mod, workerIdx); err != nil {
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
