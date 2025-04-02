package main

import (
	"flag"
	"fmt"
	"log"
	"os"
	"path/filepath"

	"github.com/jns/pfuzz/internal/simulator"
	"github.com/jns/pfuzz/pkg/utils"
)

func main() {
	flag.Parse()

	if err := utils.EnsureDirs(); err != nil {
		log.Fatal("Failed to create directories:", err)
	}

	// Create a dedicated directory for focused tests
	focusedDir := filepath.Join(utils.TMP_DIR, "focused")
	if err := os.MkdirAll(focusedDir, 0755); err != nil {
		log.Fatal("Failed to create focused directory:", err)
	}

	// Create specific test cases targeting the branch prediction logic
	testCases := []struct {
		Name        string
		Instruction uint32
		PC          uint32
		Valid       uint8
		Description string
	}{
		// Test case for B-type with negative offset
		{
			Name:        "b_negative",
			Instruction: 0xFE3086E3, // BEQ x1, x3, -20
			PC:          0x1000,
			Valid:       1,
			Description: "Branch with negative offset (should predict taken)",
		},
		// Test case for B-type with positive offset
		{
			Name:        "b_positive",
			Instruction: 0x00310663, // BEQ x2, x3, 12
			PC:          0x1000,
			Valid:       1,
			Description: "Branch with positive offset (should predict not taken)",
		},
		// Test case for JAL
		{
			Name:        "jal",
			Instruction: 0x0040006F, // JAL x0, 4
			PC:          0x1000,
			Valid:       1,
			Description: "JAL (should always predict taken)",
		},
		// Test case for compressed branch with negative offset
		{
			Name:        "c_beqz_negative",
			Instruction: 0xC0FD, // C.BEQZ x15, -4
			PC:          0x1000,
			Valid:       1,
			Description: "Compressed branch with negative offset (should predict taken)",
		},
		// Test case for compressed branch with positive offset
		{
			Name:        "c_beqz_positive",
			Instruction: 0xC001, // C.BEQZ x8, 2
			PC:          0x1000,
			Valid:       1,
			Description: "Compressed branch with positive offset (should predict not taken)",
		},
		// Test case for compressed jump
		{
			Name:        "c_j",
			Instruction: 0xA001, // C.J 2
			PC:          0x1000,
			Valid:       1,
			Description: "Compressed jump (should always predict taken)",
		},
		// Add more test cases as needed
	}

	// Prepare simulators
	ivSim := simulator.NewIVerilogSimulator(focusedDir)
	vlSim := simulator.NewVerilatorSimulator(focusedDir)

	if err := ivSim.Compile(); err != nil {
		log.Fatal("Failed to compile IVerilog:", err)
	}

	if err := vlSim.Compile(); err != nil {
		log.Fatal("Failed to compile Verilator:", err)
	}

	// Run all test cases
	fmt.Println("Running focused test cases...")
	for i, tc := range testCases {
		fmt.Printf("\n=== Test case: %s ===\n", tc.Name)
		fmt.Printf("Description: %s\n", tc.Description)
		fmt.Printf("Instruction: 0x%08x  PC: 0x%08x  Valid: %d\n",
			tc.Instruction, tc.PC, tc.Valid)

		// Create test-specific files
		testCaseDir := filepath.Join(focusedDir, fmt.Sprintf("case_%d_%s", i, tc.Name))
		if err := os.MkdirAll(testCaseDir, 0755); err != nil {
			log.Printf("Failed to create test case directory: %v", err)
			continue
		}

		// Write input files
		inputPath := filepath.Join(testCaseDir, "input.hex")
		pcPath := filepath.Join(testCaseDir, "pc.hex")
		validPath := filepath.Join(testCaseDir, "valid.hex")
		ivTakenPath := filepath.Join(testCaseDir, "iv_taken.hex")
		ivTargetPath := filepath.Join(testCaseDir, "iv_target.hex")
		vlTakenPath := filepath.Join(testCaseDir, "vl_taken.hex")
		vlTargetPath := filepath.Join(testCaseDir, "vl_target.hex")

		utils.WriteHexFile(inputPath, tc.Instruction)
		utils.WriteHexFile(pcPath, tc.PC)
		utils.WriteBinFile(validPath, tc.Valid)

		// Run simulations
		if err := ivSim.RunTest(inputPath, pcPath, validPath, ivTakenPath, ivTargetPath); err != nil {
			log.Printf("IVerilog simulation failed: %v", err)
			continue
		}

		ivResult, err := simulator.ReadSimResultsFromFiles(ivTakenPath, ivTargetPath)
		if err != nil {
			log.Printf("Failed to read IVerilog results: %v", err)
			continue
		}

		if err := vlSim.RunTest(inputPath, pcPath, validPath, vlTakenPath, vlTargetPath); err != nil {
			log.Printf("Verilator simulation failed: %v", err)
			continue
		}

		vlResult, err := simulator.ReadSimResultsFromFiles(vlTakenPath, vlTargetPath)
		if err != nil {
			log.Printf("Failed to read Verilator results: %v", err)
			continue
		}

		// Compare results
		fmt.Printf("IVerilog:  taken=%d target=0x%08x\n",
			ivResult.BranchTaken, ivResult.BranchPc)
		fmt.Printf("Verilator: taken=%d target=0x%08x\n",
			vlResult.BranchTaken, vlResult.BranchPc)

		if ivResult.BranchTaken != vlResult.BranchTaken ||
			ivResult.BranchPc != vlResult.BranchPc {
			fmt.Printf("MISMATCH DETECTED\n")

			// Save to mismatches directory for further analysis
			mismatchDir := filepath.Join(utils.MISMATCHES_DIR, fmt.Sprintf("focused_%s", tc.Name))
			os.MkdirAll(mismatchDir, 0755)

			utils.CopyFile(inputPath, filepath.Join(mismatchDir, "input.hex"))
			utils.CopyFile(pcPath, filepath.Join(mismatchDir, "pc.hex"))
			utils.CopyFile(validPath, filepath.Join(mismatchDir, "valid.hex"))
			utils.CopyFile(ivTakenPath, filepath.Join(mismatchDir, "iv_taken.hex"))
			utils.CopyFile(ivTargetPath, filepath.Join(mismatchDir, "iv_target.hex"))
			utils.CopyFile(vlTakenPath, filepath.Join(mismatchDir, "vl_taken.hex"))
			utils.CopyFile(vlTargetPath, filepath.Join(mismatchDir, "vl_target.hex"))

			// Also create a summary file
			summaryPath := filepath.Join(utils.MISMATCHES_DIR, fmt.Sprintf("focused_%s.txt", tc.Name))
			file, err := os.Create(summaryPath)
			if err == nil {
				fmt.Fprintf(file, "Focused test case: %s\n", tc.Name)
				fmt.Fprintf(file, "Description: %s\n\n", tc.Description)
				fmt.Fprintf(file, "Inputs:\n")
				fmt.Fprintf(file, "  rdata=0x%08x\n  pc=0x%08x\n  valid=%d\n\n",
					tc.Instruction, tc.PC, tc.Valid)
				fmt.Fprintf(file, "Results:\n")
				fmt.Fprintf(file, "  IVerilog: taken=%d pc=0x%08x\n",
					ivResult.BranchTaken, ivResult.BranchPc)
				fmt.Fprintf(file, "  Verilator: taken=%d pc=0x%08x\n",
					vlResult.BranchTaken, vlResult.BranchPc)
				file.Close()
			}
		} else {
			fmt.Printf("Results match\n")
		}
	}
}
