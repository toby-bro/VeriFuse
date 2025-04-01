package main

import (
	"flag"
	"fmt"
	"log"

	"github.com/jns/pfuzz/internal/simulator"
	"github.com/jns/pfuzz/pkg/utils"
)

func main() {
	flag.Parse()

	if err := utils.EnsureDirs(); err != nil {
		log.Fatal("Failed to create directories:", err)
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
	ivSim := simulator.NewIVerilogSimulator()
	vlSim := simulator.NewVerilatorSimulator()

	if err := ivSim.Compile(); err != nil {
		log.Fatal("Failed to compile IVerilog:", err)
	}

	if err := vlSim.Compile(); err != nil {
		log.Fatal("Failed to compile Verilator:", err)
	}

	// Run all test cases
	fmt.Println("Running focused test cases...")
	for _, tc := range testCases {
		fmt.Printf("\n=== Test case: %s ===\n", tc.Name)
		fmt.Printf("Description: %s\n", tc.Description)
		fmt.Printf("Instruction: 0x%08x  PC: 0x%08x  Valid: %d\n",
			tc.Instruction, tc.PC, tc.Valid)

		// Write input files
		utils.WriteHexFile(utils.TmpPath("input.hex"), tc.Instruction)
		utils.WriteHexFile(utils.TmpPath("pc.hex"), tc.PC)
		utils.WriteBinFile(utils.TmpPath("valid.hex"), tc.Valid)

		// Run simulations
		if err := ivSim.Run(); err != nil {
			log.Printf("IVerilog simulation failed: %v", err)
			continue
		}

		ivResult, err := ivSim.ReadResults()
		if err != nil {
			log.Printf("Failed to read IVerilog results: %v", err)
			continue
		}

		if err := vlSim.Run(); err != nil {
			log.Printf("Verilator simulation failed: %v", err)
			continue
		}

		vlResult, err := vlSim.ReadResults()
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
		} else {
			fmt.Printf("Results match\n")
		}
	}
}
