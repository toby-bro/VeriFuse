package fuzz

import (
	"bytes"
	"fmt"
	"log"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"time"

	"github.com/jns/pfuzz/internal/analyzer"
	"github.com/jns/pfuzz/internal/simulator"
	"github.com/jns/pfuzz/internal/testgen"
	"github.com/jns/pfuzz/pkg/utils"
)

const (
	// Source file names
	ORIGINAL_VERILOG_FILE = "ibex_branch_predict.sv"
	TESTBENCH_FILE        = "testbench.sv"
	IVERILOG_EXEC         = "ibex_sim_iv"

	// Test file names
	TEST_FILE_INPUT  = "input.hex"
	TEST_FILE_PC     = "pc.hex"
	TEST_FILE_VALID  = "valid.hex"
	TEST_FILE_TAKEN  = "taken.hex"
	TEST_FILE_TARGET = "target.hex"
)

// Test file prefixes for different simulators
const (
	IV_PREFIX = "iv_"
	VL_PREFIX = "vl_"
)

// Fuzzer is the main fuzzing orchestrator
type Fuzzer struct {
	stats    *Stats
	strategy Strategy
	workers  int
	verbose  bool
	seed     int64
	debug    *utils.DebugLogger
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
		debug:    utils.NewDebugLogger(verbose),
	}
}

func PrepareSVFile(initialVerilogFile string, mockedVerilogPath string) error {
	// Analyze and mock Verilog file
	content, err := analyzer.AnalyzeVerilogFile(initialVerilogFile)
	if err != nil {
		return fmt.Errorf("failed to analyze Verilog file: %v", err)
	}

	// Create the mocked verilog file
	if err := utils.WriteFileContent(mockedVerilogPath, content); err != nil {
		return fmt.Errorf("failed to write mocked SV file: %v", err)
	}
	log.Printf("Created mocked SystemVerilog file: %s", mockedVerilogPath)

	// Verify the file exists
	if _, err := os.Stat(mockedVerilogPath); os.IsNotExist(err) {
		return fmt.Errorf("mocked verilog file was not created at %s", mockedVerilogPath)
	}
	return nil
}

func addMockedSuffix(filename string) string {
	ext := filepath.Ext(filename)
	base := strings.TrimSuffix(filename, ext)
	newFilename := base + "_mocked" + ext
	return newFilename
}

// Setup prepares the environment for fuzzing
func (f *Fuzzer) Setup() error {
	// Ensure directories exist first
	if err := utils.EnsureDirs(); err != nil {
		return fmt.Errorf("failed to create directories: %v", err)
	}

	mockedVerilogFile := addMockedSuffix(ORIGINAL_VERILOG_FILE)
	mockedVerilogPath := filepath.Join(utils.TMP_DIR, addMockedSuffix(ORIGINAL_VERILOG_FILE))

	if err := PrepareSVFile(ORIGINAL_VERILOG_FILE, mockedVerilogPath); err != nil {
		return err
	}

	// Generate testbenches
	gen := testgen.NewGenerator()
	if err := gen.GenerateTestbenches(); err != nil {
		return fmt.Errorf("failed to generate testbenches: %v", err)
	}

	testbenchPath := filepath.Join(utils.TMP_DIR, TESTBENCH_FILE)
	if _, err := os.Stat(testbenchPath); os.IsNotExist(err) {
		return fmt.Errorf("testbench file was not created at %s", testbenchPath)
	}

	f.debug.Log("Created testbenches in %s directory", utils.TMP_DIR)

	// Create a setup directory for compilation
	setupDir := filepath.Join(utils.TMP_DIR, "setup")
	if err := os.MkdirAll(setupDir, 0755); err != nil {
		return fmt.Errorf("failed to create setup directory: %v", err)
	}

	// Copy the necessary files to the setup directory
	setupVerilogPath := filepath.Join(setupDir, mockedVerilogFile)
	setupTestbenchPath := filepath.Join(setupDir, TESTBENCH_FILE)

	if err := utils.CopyFile(mockedVerilogPath, setupVerilogPath); err != nil {
		return fmt.Errorf("failed to copy Verilog file to setup dir: %v", err)
	}

	if err := utils.CopyFile(testbenchPath, setupTestbenchPath); err != nil {
		return fmt.Errorf("failed to copy testbench to setup dir: %v", err)
	}

	// Verify the copied files exist in the setup directory
	if _, err := os.Stat(setupVerilogPath); os.IsNotExist(err) {
		return fmt.Errorf("failed to verify copied verilog file in setup dir: %s", setupVerilogPath)
	}

	if _, err := os.Stat(setupTestbenchPath); os.IsNotExist(err) {
		return fmt.Errorf("failed to verify copied testbench in setup dir: %s", setupTestbenchPath)
	}

	// Test IVerilog compilation
	if err := testIVerilog(setupDir, mockedVerilogFile); err != nil {
		return fmt.Errorf("iverilog test failed: %v", err)
	}
	if err := testVerilator(setupDir); err != nil {
		return fmt.Errorf("verilator test failed: %v", err)
	}

	return nil
}

func testIVerilog(setupDir string, mockedVerilogFile string) error {

	// Create a test file to verify IVerilog works correctly
	testFile := filepath.Join(setupDir, "test.sv")
	testContent := `
    module test;
      initial begin
        $display("IVerilog test");
        $finish;
      end
    endmodule
    `
	if err := os.WriteFile(testFile, []byte(testContent), 0644); err != nil {
		return fmt.Errorf("failed to write IVerilog test file: %v", err)
	}

	// Test IVerilog with a simple compilation first - use relative paths and proper working directory
	testExecPath := "test"
	cmd := exec.Command("iverilog", "-o", testExecPath, "test.sv")
	cmd.Dir = setupDir
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	if err := cmd.Run(); err != nil {
		return fmt.Errorf("iverilog basic test failed, check your installation: %v - %s", err, stderr.String())
	}

	// Verify the test executable exists
	testFullPath := filepath.Join(setupDir, testExecPath)
	if _, err := os.Stat(testFullPath); os.IsNotExist(err) {
		return fmt.Errorf("iverilog test executable not created at %s", testFullPath)
	}

	// Run the test with proper working directory
	testCmd := exec.Command("./test")
	testCmd.Dir = setupDir
	stderr.Reset()
	testCmd.Stderr = &stderr
	var stdout bytes.Buffer
	testCmd.Stdout = &stdout
	if err := testCmd.Run(); err != nil {
		return fmt.Errorf("failed to run iverilog test executable: %v - %s", err, stderr.String())
	}

	// Log the test output for debugging
	log.Printf("IVerilog test output: %s", stdout.String())

	// Compile simulators using local file paths and working directory with more robust error handling
	log.Println("Compiling iverilog in setup directory...")
	ivCmd := exec.Command("iverilog", "-o", IVERILOG_EXEC,
		mockedVerilogFile, TESTBENCH_FILE, "-g2012")
	ivCmd.Dir = setupDir
	stderr.Reset()
	ivCmd.Stderr = &stderr
	if err := ivCmd.Run(); err != nil {
		return fmt.Errorf("iverilog compilation failed using direct invocation: %v - %s", err, stderr.String())
	}

	// Verify iverilog executable was created
	ivExecPath := filepath.Join(setupDir, IVERILOG_EXEC)
	if _, err := os.Stat(ivExecPath); os.IsNotExist(err) {
		return fmt.Errorf("iverilog executable not created at %s", ivExecPath)
	}

	// Test the iverilog simulator to ensure it's valid
	// This will fail without proper input files, but should at least start without errors
	ivTestCmd := exec.Command("./" + IVERILOG_EXEC)
	ivTestCmd.Dir = setupDir
	stderr.Reset()
	ivTestCmd.Stderr = &stderr
	err := ivTestCmd.Run()
	// We expect it to fail because we don't have input files, but check stderr
	if err != nil && !strings.Contains(stderr.String(), "fopen") {
		// Only return an error if it's not the expected "file not found" error
		return fmt.Errorf("iverilog simulator executable failed unexpectedly: %s", stderr.String())
	}

	log.Println("Successfully compiled with iverilog")
	return nil
}

func testVerilator(setupDir string) error {
	// For verilator, use the simulator with proper error handling
	vlsim := simulator.NewVerilatorSimulator(setupDir)
	if err := vlsim.Compile(); err != nil {
		return fmt.Errorf("failed to compile with verilator: %v", err)
	}
	log.Println("Successfully compiled with verilator")
	return nil
}

// Run performs the fuzzing
func (f *Fuzzer) Run(numTests int) error {
	f.debug.Log("Starting fuzzing with %d test cases using strategy: %s\n", numTests, f.strategy.Name())

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
		f.debug.Log("Found %d mismatches between iverilog and verilator!\n", f.stats.Mismatches)
		return fmt.Errorf("%d mismatches found", f.stats.Mismatches)
	}

	f.debug.Log("No mismatches found after %d tests.\n", numTests)
	return nil
}

// runSimulator executes a simulator with the provided inputs and returns simulation results
func (f *Fuzzer) runSimulator(simName string, sim simulator.Simulator, i int,
	inputPath, pcPath, validPath, takenPath, targetPath string) (simulator.SimResult, bool) {

	// Run simulator
	if err := sim.RunTest(inputPath, pcPath, validPath, takenPath, targetPath); err != nil {
		if f.verbose {
			log.Printf("Test %d %s failed: %v", i, simName, err)
		}
		f.stats.AddSimError()
		return simulator.SimResult{}, false
	}

	// Verify output files exist
	if !utils.FileExists(takenPath) || !utils.FileExists(targetPath) {
		if f.verbose {
			log.Printf("Test %d %s output files missing after simulation", i, simName)
		}
		f.stats.AddSimError()
		return simulator.SimResult{}, false
	}

	// Read results
	result, err := simulator.ReadSimResultsFromFiles(takenPath, targetPath)
	if err != nil {
		if f.verbose {
			log.Printf("Test %d %s results read failed: %v", i, simName, err)
		}
		f.stats.AddSimError()
		return simulator.SimResult{}, false
	}

	return result, true
}

// worker is a goroutine that processes test cases
func (f *Fuzzer) worker(wg *sync.WaitGroup, testCases <-chan int, numTests int) {
	defer wg.Done()

	mockedVerilogFile := addMockedSuffix(ORIGINAL_VERILOG_FILE)

	// Each worker gets its own simulator instances and working directory
	workerID := fmt.Sprintf("worker_%d", time.Now().UnixNano())
	workerDir := filepath.Join(utils.TMP_DIR, workerID)

	f.debug.Printf("[%s]: Creating worker directory at %s", workerID, workerDir)

	// Create worker-specific directory
	if err := os.MkdirAll(workerDir, 0755); err != nil {
		log.Printf("Failed to create worker directory %s: %v", workerDir, err)
		return
	}

	// Use a WaitGroup to track when it's safe to clean up
	var workerWg sync.WaitGroup
	workerWg.Add(1)

	// Handle deferred cleanup with a WaitGroup to ensure all operations are complete
	defer func() {
		// Sync point - all operations within worker must complete before cleanup
		workerWg.Done()
		workerWg.Wait()

		// Now it's safe to remove the directory
		//time.Sleep(500 * time.Millisecond) // Add longer delay for safety
		if err := os.RemoveAll(workerDir); err != nil {
			log.Printf("Warning: Failed to clean up worker directory %s: %v", workerDir, err)
		} else if f.verbose {
			log.Printf("Cleaned up worker directory: %s", workerDir)
		}
	}()

	// Copy all required files to the worker directory
	f.debug.Printf("[%s]: Copying source files to worker directory", workerID)
	setupFiles := []string{
		mockedVerilogFile,
		TESTBENCH_FILE,
	}

	for _, filename := range setupFiles {
		srcPath := filepath.Join(utils.TMP_DIR, filename)
		dstPath := filepath.Join(workerDir, filename)
		if err := utils.CopyFile(srcPath, dstPath); err != nil {
			log.Printf("Failed to copy %s to worker directory: %v", filename, err)
			return
		}

		// Verify the file was copied successfully
		if fi, err := os.Stat(dstPath); err != nil || fi.Size() == 0 {
			f.debug.Printf("[%s]: File %s not copied correctly, size: %d, error: %v",
				workerID, dstPath, fi.Size(), err)
			return
		}
		f.debug.Printf("[%s]: Successfully copied %s", workerID, filename)
	}

	// Create worker-specific simulators
	f.debug.Printf("[%s]: Creating simulators", workerID)
	ivsim := simulator.NewIVerilogSimulator(workerDir, f.verbose)
	vlsim := simulator.NewVerilatorSimulator(workerDir)

	// Check if iverilog is available on this system
	ivCheck := exec.Command("which", "iverilog")
	ivCheckOutput, err := ivCheck.Output()
	if err != nil {
		f.debug.Printf("[%s]: iverilog not found in PATH: %v", workerID, err)
	} else {
		f.debug.Printf("[%s]: iverilog found at: %s", workerID, strings.TrimSpace(string(ivCheckOutput)))
	}

	// Try to compile directly with system command first
	f.debug.Printf("[%s]: Running direct iverilog compilation to test", workerID)
	directCmd := exec.Command("iverilog", "-o", IVERILOG_EXEC,
		mockedVerilogFile, TESTBENCH_FILE, "-g2012")
	directCmd.Dir = workerDir
	var directStderr bytes.Buffer
	directCmd.Stderr = &directStderr
	if directErr := directCmd.Run(); directErr != nil {
		f.debug.Printf("[%s]: Direct iverilog compilation failed: %v - %s",
			workerID, directErr, directStderr.String())
	} else {
		f.debug.Printf("[%s]: Direct iverilog compilation succeeded", workerID)
	}

	// Now try the actual Compile method
	f.debug.Printf("[%s]: Compiling IVerilog simulator", workerID)
	if err := ivsim.Compile(); err != nil {
		log.Printf("Failed to compile IVerilog in worker %s: %v", workerID, err)
		return
	}

	// Verify the iverilog executable exists and has correct permissions
	ivExecPath := ivsim.GetExecPath()
	f.debug.Printf("[%s]: Verifying IVerilog executable at %s", workerID, ivExecPath)
	fileInfo, err := os.Stat(ivExecPath)
	if err != nil {
		f.debug.Printf("[%s]: Executable stat failed: %v", workerID, err)
		if os.IsNotExist(err) {
			// List directory contents
			files, _ := os.ReadDir(workerDir)
			fileList := make([]string, 0, len(files))
			for _, f := range files {
				fileList = append(fileList, f.Name())
			}
			f.debug.Printf("[%s]: Directory contents: %v", workerID, fileList)
		}
		return
	}

	f.debug.Printf("[%s]: Executable found, size: %d bytes, mode: %s",
		workerID, fileInfo.Size(), fileInfo.Mode())

	// Make sure it's executable
	if fileInfo.Mode().Perm()&0111 == 0 {
		f.debug.Printf("[%s]: Adding execute permission to %s", workerID, ivExecPath)
		if err := os.Chmod(ivExecPath, 0755); err != nil {
			f.debug.Printf("[%s]: chmod failed: %v", workerID, err)
			return
		}
	}

	// Try to execute with "file" command to verify it's a valid executable
	fileCmd := exec.Command("file", ivExecPath)
	fileOutput, _ := fileCmd.Output()
	f.debug.Printf("[%s]: file command output: %s", workerID, string(fileOutput))

	// Compile Verilator as normal
	if err := vlsim.Compile(); err != nil {
		log.Printf("Failed to compile Verilator in worker %s: %v", workerID, err)
		return
	}

	// Process test cases - do this in a new goroutine so our defer handler waits for it
	workerWg.Add(1)
	go func() {
		defer workerWg.Done()

		for i := range testCases {
			testCase := f.strategy.GenerateTestCase(i)
			f.stats.AddTest()

			// Create a test-specific directory within the worker directory
			testDir := filepath.Join(workerDir, fmt.Sprintf("test_%d", i))
			if err := os.MkdirAll(testDir, 0755); err != nil {
				if f.verbose {
					log.Printf("Test %d failed to create test directory: %v", i, err)
				}
				f.stats.AddSimError()
				continue
			}

			// Write input files directly to the test directory
			inputPath := filepath.Join(testDir, TEST_FILE_INPUT)
			pcPath := filepath.Join(testDir, TEST_FILE_PC)
			validPath := filepath.Join(testDir, TEST_FILE_VALID)
			ivTakenPath := filepath.Join(testDir, IV_PREFIX+TEST_FILE_TAKEN)
			ivTargetPath := filepath.Join(testDir, IV_PREFIX+TEST_FILE_TARGET)
			vlTakenPath := filepath.Join(testDir, VL_PREFIX+TEST_FILE_TAKEN)
			vlTargetPath := filepath.Join(testDir, VL_PREFIX+TEST_FILE_TARGET)

			// Write test inputs
			if err := utils.WriteHexFile(inputPath, testCase.FetchRdata); err != nil {
				if f.verbose {
					log.Printf("Test %d failed to write input file: %v", i, err)
				}
				f.stats.AddSimError()
				continue
			}
			if err := utils.WriteHexFile(pcPath, testCase.FetchPc); err != nil {
				if f.verbose {
					log.Printf("Test %d failed to write pc file: %v", i, err)
				}
				f.stats.AddSimError()
				continue
			}
			if err := utils.WriteBinFile(validPath, testCase.FetchValid); err != nil {
				if f.verbose {
					log.Printf("Test %d failed to write valid file: %v", i, err)
				}
				f.stats.AddSimError()
				continue
			}

			// Run IVerilog simulator using the helper function
			ivResult, ivSuccess := f.runSimulator("iverilog", ivsim, i,
				inputPath, pcPath, validPath, ivTakenPath, ivTargetPath)
			if !ivSuccess {
				continue
			}

			// Run Verilator simulator using the same helper function
			vlResult, vlSuccess := f.runSimulator("verilator", vlsim, i,
				inputPath, pcPath, validPath, vlTakenPath, vlTargetPath)
			if !vlSuccess {
				continue
			}

			// Compare results
			if ivResult.BranchTaken != vlResult.BranchTaken || ivResult.BranchPc != vlResult.BranchPc {
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

				// Save the complete test case files for replay
				mismatchDir := filepath.Join(utils.MISMATCHES_DIR, fmt.Sprintf("mismatch_%d", i))
				os.MkdirAll(mismatchDir, 0755)

				// Copy all input and output files to the mismatch directory
				utils.CopyFile(inputPath, filepath.Join(mismatchDir, TEST_FILE_INPUT))
				utils.CopyFile(pcPath, filepath.Join(mismatchDir, TEST_FILE_PC))
				utils.CopyFile(validPath, filepath.Join(mismatchDir, TEST_FILE_VALID))
				utils.CopyFile(ivTakenPath, filepath.Join(mismatchDir, IV_PREFIX+TEST_FILE_TAKEN))
				utils.CopyFile(ivTargetPath, filepath.Join(mismatchDir, IV_PREFIX+TEST_FILE_TARGET))
				utils.CopyFile(vlTakenPath, filepath.Join(mismatchDir, VL_PREFIX+TEST_FILE_TAKEN))
				utils.CopyFile(vlTargetPath, filepath.Join(mismatchDir, VL_PREFIX+TEST_FILE_TARGET))

				// Create a summary file with all information
				filename := filepath.Join(utils.MISMATCHES_DIR, fmt.Sprintf("mismatch_%d.txt", i))
				file, err := os.Create(filename)
				if err == nil {
					fmt.Fprintf(file, "Test case %d\n", i)
					fmt.Fprintf(file, "Inputs:\n")
					fmt.Fprintf(file, "  rdata=0x%08x\n  pc=0x%08x\n  valid=%d\n",
						testCase.FetchRdata, testCase.FetchPc, testCase.FetchValid)
					fmt.Fprintf(file, "\nDecoded: %s\n", instFields)
					fmt.Fprintf(file, "\nResults:\n")
					fmt.Fprintf(file, "  IVerilog: taken=%d pc=0x%08x\n",
						ivResult.BranchTaken, ivResult.BranchPc)
					fmt.Fprintf(file, "  Verilator: taken=%d pc=0x%08x\n",
						vlResult.BranchTaken, vlResult.BranchPc)

					if branchTakenMismatch {
						fmt.Fprintf(file, "\nTAKEN MISMATCH\n")
					}
					if pcMismatch {
						fmt.Fprintf(file, "\nTARGET MISMATCH (diff=0x%x)\n",
							ivResult.BranchPc^vlResult.BranchPc)
					}

					file.Close()
					log.Printf("  Saved to %s for reproduction\n", filename)
				}

				f.stats.AddMismatch(testCase)
			}

			// Explicitly clean up test files after each test to avoid directory filling up
			if !f.verbose {
				os.RemoveAll(testDir)
			}
		}
	}()
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
