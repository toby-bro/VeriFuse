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
	// Ensure directories exist
	if err := utils.EnsureDirs(); err != nil {
		return fmt.Errorf("failed to create directories: %v", err)
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
		if err := utils.WriteHexFile(filepath.Join(utils.TMP_DIR, "input.hex"), testCase.FetchRdata); err != nil {
			if f.verbose {
				log.Printf("Test %d failed to write input file: %v", i, err)
			}
			f.stats.AddSimError()
			continue
		}
		if err := utils.WriteHexFile(filepath.Join(utils.TMP_DIR, "pc.hex"), testCase.FetchPc); err != nil {
			if f.verbose {
				log.Printf("Test %d failed to write pc file: %v", i, err)
			}
			f.stats.AddSimError()
			continue
		}
		if err := utils.WriteBinFile(filepath.Join(utils.TMP_DIR, "valid.hex"), testCase.FetchValid); err != nil {
			if f.verbose {
				log.Printf("Test %d failed to write valid file: %v", i, err)
			}
			f.stats.AddSimError()
			continue
		}

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
			// Determine what fields are mismatched
			branchTakenMismatch := ivResult.BranchTaken != vlResult.BranchTaken
			pcMismatch := ivResult.BranchPc != vlResult.BranchPc

			log.Printf("Mismatch found in test %d:\n", i)
			log.Printf("  Input: rdata=0x%08x pc=0x%08x valid=%d\n",
				testCase.FetchRdata, testCase.FetchPc, testCase.FetchValid)

			// Display decoded instruction
			instFields := decodeInstruction(testCase.FetchRdata)
			log.Printf("  Decoded: %s\n", instFields)

			// Highlight the specific mismatched field
			if branchTakenMismatch {
				log.Printf("  TAKEN MISMATCH: IVerilog=%d vs Verilator=%d\n",
					ivResult.BranchTaken, vlResult.BranchTaken)
			}
			if pcMismatch {
				log.Printf("  TARGET MISMATCH: IVerilog=0x%08x vs Verilator=0x%08x (diff=0x%x)\n",
					ivResult.BranchPc, vlResult.BranchPc, ivResult.BranchPc^vlResult.BranchPc)
			}

			f.stats.AddMismatch(testCase)

			// Save testcase to file for reproduction in mismatches directory
			filename := filepath.Join(utils.MISMATCHES_DIR, fmt.Sprintf("mismatch_%d.txt", i))
			file, err := os.Create(filename)
			if err == nil {
				fmt.Fprintf(file, "Test case %d\n", i)
				fmt.Fprintf(file, "Inputs:\n")
				fmt.Fprintf(file, "  rdata=0x%08x\n  pc=0x%08x\n  valid=%d\n",
					testCase.FetchRdata, testCase.FetchPc, testCase.FetchValid)
				fmt.Fprintf(file, "\nResults:\n")
				fmt.Fprintf(file, "  IVerilog: taken=%d pc=0x%08x\n",
					ivResult.BranchTaken, ivResult.BranchPc)
				fmt.Fprintf(file, "  Verilator: taken=%d pc=0x%08x\n",
					vlResult.BranchTaken, vlResult.BranchPc)
				file.Close()
				log.Printf("  Saved to %s for reproduction\n", filename)
			}
		}
	}
}

// decodeInstruction returns a human-readable description of an instruction
func decodeInstruction(instr uint32) string {
	opcode := instr & 0x7F

	switch opcode {
	case 0x63: // BRANCH
		funct3 := (instr >> 12) & 0x7
		rs1 := (instr >> 15) & 0x1F
		rs2 := (instr >> 20) & 0x1F
		imm12 := (instr >> 31) & 0x1
		imm10_5 := (instr >> 25) & 0x3F
		imm4_1 := (instr >> 8) & 0xF
		imm11 := (instr >> 7) & 0x1

		// Reconstruct the immediate value
		imm := (imm12 << 12) | (imm11 << 11) | (imm10_5 << 5) | (imm4_1 << 1)
		// Sign extend
		if imm12 > 0 {
			imm |= 0xFFFFE000
		}

		branchTypes := []string{"BEQ", "BNE", "???", "???", "BLT", "BGE", "BLTU", "BGEU"}
		return fmt.Sprintf("BRANCH %s rs1=%d rs2=%d imm=0x%x (%d)",
			branchTypes[funct3], rs1, rs2, imm, int32(imm))

	case 0x6F: // JAL
		rd := (instr >> 7) & 0x1F
		imm20 := (instr >> 31) & 0x1
		imm10_1 := (instr >> 21) & 0x3FF
		imm11 := (instr >> 20) & 0x1
		imm19_12 := (instr >> 12) & 0xFF

		// Reconstruct the immediate value
		imm := (imm20 << 20) | (imm19_12 << 12) | (imm11 << 11) | (imm10_1 << 1)
		// Sign extend
		if imm20 > 0 {
			imm |= 0xFFE00000
		}

		return fmt.Sprintf("JAL rd=%d imm=0x%x (%d)", rd, imm, int32(imm))

	case 0x01: // Compressed
		funct3 := (instr >> 13) & 0x7
		if funct3 == 0x5 || funct3 == 0x1 {
			// C.J or C.JAL
			cjType := "C.J"
			if funct3 == 0x1 {
				cjType = "C.JAL"
			}
			imm11 := (instr >> 12) & 0x1
			imm4 := (instr >> 11) & 0x1
			imm9_8 := (instr >> 9) & 0x3
			imm10 := (instr >> 8) & 0x1
			imm6 := (instr >> 7) & 0x1
			imm7 := (instr >> 6) & 0x1
			imm3_1 := (instr >> 3) & 0x7
			imm5 := (instr >> 2) & 0x1

			// Reconstruct the immediate
			imm := (imm11 << 11) | (imm10 << 10) | (imm9_8 << 8) | (imm7 << 7) |
				(imm6 << 6) | (imm5 << 5) | (imm4 << 4) | (imm3_1 << 1)
			// Sign extend
			if imm11 > 0 {
				imm |= 0xFFFFF800
			}

			return fmt.Sprintf("%s imm=0x%x (%d)", cjType, imm, int32(imm))

		} else if funct3 == 0x6 || funct3 == 0x7 {
			// C.BEQZ or C.BNEZ
			cbType := "C.BEQZ"
			if funct3 == 0x7 {
				cbType = "C.BNEZ"
			}
			imm8 := (instr >> 12) & 0x1
			imm4_3 := (instr >> 10) & 0x3
			imm7_6 := (instr >> 5) & 0x3
			imm2_1 := (instr >> 3) & 0x3
			imm5 := (instr >> 2) & 0x1
			rs1 := (instr >> 7) & 0x7

			// Reconstruct the immediate
			imm := (imm8 << 8) | (imm7_6 << 6) | (imm5 << 5) | (imm4_3 << 3) | (imm2_1 << 1)
			// Sign extend
			if imm8 > 0 {
				imm |= 0xFFFFFE00
			}

			return fmt.Sprintf("%s rs1=%d imm=0x%x (%d)", cbType, rs1+8, imm, int32(imm))
		}

		return fmt.Sprintf("COMPRESSED 0x%04x", instr&0xFFFF)

	default:
		return fmt.Sprintf("UNKNOWN opcode=0x%02x", opcode)
	}
}
