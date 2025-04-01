package fuzz

import (
	"fmt"
	"log"
	"os"
	"path/filepath"
	"sync"

	"github.com/jns/pfuzz/internal/analyzer"
	"github.com/jns/pfuzz/internal/simulator"
	"github.com/jns/pfuzz/internal/testgen"
	"github.com/jns/pfuzz/pkg/utils"
)

// Fuzzer is the main fuzzing orchestrator
type Fuzzer struct {
	stats    *Stats
	strategy Strategy
	workers  int
	verbose  bool
	seed     int64
}

// NewFuzzer creates a new fuzzer instance
func NewFuzzer(strategy string, workers int, verbose bool, seed int64) *Fuzzer {
	var s Strategy
	switch strategy {
	case "simple":
		s = &SimpleStrategy{seed: seed}
	case "mutation":
		s = &MutationStrategy{seed: seed}
	default:
		s = &OpcodeAwareStrategy{seed: seed}
	}

	return &Fuzzer{
		stats:    NewStats(),
		strategy: s,
		workers:  workers,
		verbose:  verbose,
		seed:     seed,
	}
}

// Setup prepares the environment for fuzzing
func (f *Fuzzer) Setup() error {
	// Ensure tmp_gen directory exists
	if err := utils.EnsureTmpDir(); err != nil {
		return fmt.Errorf("failed to create temporary directory: %v", err)
	}

	// Analyze and mock Verilog file
	content, err := analyzer.AnalyzeVerilogFile("ibex_branch_predict.sv")
	if err != nil {
		return fmt.Errorf("failed to analyze Verilog file: %v", err)
	}

	// Write processed content to tmp_gen directory
	if err := utils.WriteFileContent(filepath.Join(utils.TMP_DIR, "ibex_branch_predict_mocked.sv"), content); err != nil {
		return fmt.Errorf("failed to write mocked SV file: %v", err)
	}
	log.Printf("Created mocked SystemVerilog file: %s", filepath.Join(utils.TMP_DIR, "ibex_branch_predict_mocked.sv"))

	// Generate testbenches
	gen := testgen.NewGenerator()
	if err := gen.GenerateTestbenches(); err != nil {
		return fmt.Errorf("failed to generate testbenches: %v", err)
	}
	log.Printf("Created testbenches in %s directory", utils.TMP_DIR)

	// Compile simulators
	ivsim := simulator.NewIVerilogSimulator()
	if err := ivsim.Compile(); err != nil {
		return fmt.Errorf("failed to compile with iverilog: %v", err)
	}
	log.Println("Successfully compiled with iverilog")

	vlsim := simulator.NewVerilatorSimulator()
	if err := vlsim.Compile(); err != nil {
		return fmt.Errorf("failed to compile with verilator: %v", err)
	}
	log.Println("Successfully compiled with verilator")

	return nil
}

// Run performs the fuzzing
func (f *Fuzzer) Run(numTests int) error {
	log.Printf("Starting fuzzing with %d test cases using strategy: %s\n", numTests, f.strategy.Name())

	// Create a worker pool for parallel fuzzing
	var wg sync.WaitGroup
	testCases := make(chan int, f.workers)

	// Progress tracking
	progressTracker := NewProgressTracker(numTests, f.stats)
	progressTracker.Start()
	defer progressTracker.Stop()

	// Start worker goroutines
	for w := 0; w < f.workers; w++ {
		wg.Add(1)
		go f.worker(&wg, testCases, numTests)
	}

	// Feed test cases to workers
	for i := 0; i < numTests; i++ {
		testCases <- i
	}
	close(testCases)

	// Wait for all workers to finish
	wg.Wait()

	// Print summary
	f.stats.PrintSummary()

	if f.stats.Mismatches > 0 {
		log.Printf("Found %d mismatches between iverilog and verilator!\n", f.stats.Mismatches)
		return fmt.Errorf("%d mismatches found", f.stats.Mismatches)
	}

	log.Printf("No mismatches found after %d tests.\n", numTests)
	return nil
}

// worker is a goroutine that processes test cases
func (f *Fuzzer) worker(wg *sync.WaitGroup, testCases <-chan int, numTests int) {
	defer wg.Done()

	ivsim := simulator.NewIVerilogSimulator()
	vlsim := simulator.NewVerilatorSimulator()

	for i := range testCases {
		testCase := f.strategy.GenerateTestCase(i)
		f.stats.AddTest()

		// Write input files
		utils.WriteHexFile(filepath.Join(utils.TMP_DIR, "input.hex"), testCase.FetchRdata)
		utils.WriteHexFile(filepath.Join(utils.TMP_DIR, "pc.hex"), testCase.FetchPc)
		utils.WriteBinFile(filepath.Join(utils.TMP_DIR, "valid.hex"), testCase.FetchValid)

		// Run IVerilog simulation
		if err := ivsim.Run(); err != nil {
			if f.verbose {
				log.Printf("Test %d iverilog failed: %v", i, err)
			}
			f.stats.AddSimError()
			continue
		}
		ivResult, err := ivsim.ReadResults()
		if err != nil {
			if f.verbose {
				log.Printf("Test %d iverilog results read failed: %v", i, err)
			}
			f.stats.AddSimError()
			continue
		}

		// Run Verilator simulation
		if err := vlsim.Run(); err != nil {
			if f.verbose {
				log.Printf("Test %d verilator failed: %v", i, err)
			}
			f.stats.AddSimError()
			continue
		}
		vlResult, err := vlsim.ReadResults()
		if err != nil {
			if f.verbose {
				log.Printf("Test %d verilator results read failed: %v", i, err)
			}
			f.stats.AddSimError()
			continue
		}

		if ivResult != vlResult {
			log.Printf("Mismatch found in test %d:\n", i)
			log.Printf("  Input: rdata=0x%08x pc=0x%08x valid=%d\n",
				testCase.FetchRdata, testCase.FetchPc, testCase.FetchValid)
			log.Printf("  IVerilog: taken=%d pc=0x%08x\n",
				ivResult.BranchTaken, ivResult.BranchPc)
			log.Printf("  Verilator: taken=%d pc=0x%08x\n",
				vlResult.BranchTaken, vlResult.BranchPc)

			f.stats.AddMismatch(testCase)

			// Save testcase to file for reproduction
			filename := fmt.Sprintf("mismatch_%d.txt", i)
			file, err := os.Create(filename)
			if err == nil {
				fmt.Fprintf(file, "rdata=0x%08x\npc=0x%08x\nvalid=%d\n",
					testCase.FetchRdata, testCase.FetchPc, testCase.FetchValid)
				file.Close()
				log.Printf("  Saved to %s for reproduction\n", filename)
			}
		}
	}
}
