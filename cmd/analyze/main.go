package main

import (
	"flag"
	"fmt"
	"log"
	"os"
	"strconv"
	"strings"

	"github.com/jns/pfuzz/internal/simulator"
	"github.com/jns/pfuzz/pkg/utils"
)

func main() {
	flag.Parse()

	// Check if we have a mismatch file to analyze
	args := flag.Args()
	if len(args) < 1 {
		fmt.Println("Usage: analyze <mismatch_file.txt> [--step]")
		os.Exit(1)
	}

	mismatchFile := args[0]
	stepMode := len(args) > 1 && args[1] == "--step"

	// Parse the mismatch file
	content, err := os.ReadFile(mismatchFile)
	if err != nil {
		log.Fatalf("Failed to read mismatch file: %v", err)
	}

	var fetchRdata, fetchPc uint32
	var fetchValid uint8

	lines := strings.Split(string(content), "\n")
	for _, line := range lines {
		line = strings.TrimSpace(line)

		if strings.HasPrefix(line, "rdata=0x") {
			hex := strings.TrimPrefix(line, "rdata=0x")
			if val, err := strconv.ParseUint(hex, 16, 32); err == nil {
				fetchRdata = uint32(val)
			}
		} else if strings.HasPrefix(line, "pc=0x") {
			hex := strings.TrimPrefix(line, "pc=0x")
			if val, err := strconv.ParseUint(hex, 16, 32); err == nil {
				fetchPc = uint32(val)
			}
		} else if strings.HasPrefix(line, "valid=") {
			val := strings.TrimPrefix(line, "valid=")
			if v, err := strconv.Atoi(val); err == nil {
				fetchValid = uint8(v)
			}
		}
	}

	fmt.Printf("Analyzing mismatch with:\n")
	fmt.Printf("  Instruction: 0x%08x\n", fetchRdata)
	fmt.Printf("  PC: 0x%08x\n", fetchPc)
	fmt.Printf("  Valid: %d\n", fetchValid)

	// Decode the instruction
	fmt.Printf("Decoded instruction: %s\n\n", decodeInstruction(fetchRdata))

	// Create debug logs directory
	debugDir := "debug_logs"
	os.MkdirAll(debugDir, 0755)

	// Setup for simulation replay with debug output
	if err := utils.EnsureDirs(); err != nil {
		log.Fatal("Failed to create directories:", err)
	}

	// Write input files
	utils.WriteHexFile(utils.TmpPath("input.hex"), fetchRdata)
	utils.WriteHexFile(utils.TmpPath("pc.hex"), fetchPc)
	utils.WriteBinFile(utils.TmpPath("valid.hex"), fetchValid)

	// Add debug instrumentation to the Verilog files if in step mode
	if stepMode {
		// In step mode, modify the testbench to output detailed signals
		generateDebugTestbench()
	}

	// Run the simulations
	ivSim := simulator.NewIVerilogSimulator()
	vlSim := simulator.NewVerilatorSimulator()

	fmt.Println("Running IVerilog simulation...")
	if err := ivSim.Compile(); err != nil {
		log.Fatal("Failed to compile IVerilog:", err)
	}
	if err := ivSim.Run(); err != nil {
		log.Fatal("Failed to run IVerilog:", err)
	}
	ivResult, err := ivSim.ReadResults()
	if err != nil {
		log.Fatal("Failed to read IVerilog results:", err)
	}

	fmt.Println("Running Verilator simulation...")
	if err := vlSim.Compile(); err != nil {
		log.Fatal("Failed to compile Verilator:", err)
	}
	if err := vlSim.Run(); err != nil {
		log.Fatal("Failed to run Verilator:", err)
	}
	vlResult, err := vlSim.ReadResults()
	if err != nil {
		log.Fatal("Failed to read Verilator results:", err)
	}

	// Compare and display results
	fmt.Println("\n=== Simulation Results ===")
	fmt.Printf("IVerilog: taken=%d pc=0x%08x\n", ivResult.BranchTaken, ivResult.BranchPc)
	fmt.Printf("Verilator: taken=%d pc=0x%08x\n", vlResult.BranchTaken, vlResult.BranchPc)

	if ivResult.BranchTaken != vlResult.BranchTaken {
		fmt.Printf("\n*** BRANCH TAKEN MISMATCH ***\n")
		analyzePredictionDifference(fetchRdata)
	}

	if ivResult.BranchPc != vlResult.BranchPc {
		fmt.Printf("\n*** BRANCH TARGET MISMATCH ***\n")
		fmt.Printf("PC difference: 0x%x\n", ivResult.BranchPc^vlResult.BranchPc)
		analyzeTargetDifference(fetchRdata, fetchPc)
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

// Generate a testbench with extra debug instrumentation
func generateDebugTestbench() {
	// Create a modified testbench that outputs intermediate values
	// For now, just a placeholder for future implementation
	return
}

// Analyze why branch prediction differs
func analyzePredictionDifference(instr uint32) {
	opcode := instr & 0x7F

	fmt.Println("Analyzing branch prediction difference...")

	if opcode == 0x63 { // BRANCH
		funct3 := (instr >> 12) & 0x7
		imm12 := (instr >> 31) & 0x1
		fmt.Printf("Branch instruction with funct3=%d, sign bit=%d\n", funct3, imm12)
		fmt.Printf("Expected prediction: taken if sign bit is 1 (negative offset)\n")

		if imm12 == 1 {
			fmt.Println("This branch should be predicted taken - check if simulators differ here")
		} else {
			fmt.Println("This branch should be predicted not taken - check for bugs in condition")
		}
	} else if opcode == 0x6F { // JAL
		fmt.Println("JAL instructions should always be predicted taken")
		fmt.Println("Check if one simulator is incorrectly handling JAL cases")
	} else if opcode == 0x01 { // Compressed
		funct3 := (instr >> 13) & 0x7
		imm8 := (instr >> 12) & 0x1

		if funct3 == 0x5 || funct3 == 0x1 { // C.J or C.JAL
			fmt.Println("Compressed jump should always be predicted taken")
		} else if funct3 == 0x6 || funct3 == 0x7 { // C.BEQZ or C.BNEZ
			fmt.Printf("Compressed branch with sign bit=%d\n", imm8)
			if imm8 == 1 {
				fmt.Println("This compressed branch should be predicted taken - check if simulators differ")
			} else {
				fmt.Println("This compressed branch should be predicted not taken - check for bugs")
			}
		}
	}

	fmt.Println("\nPossible issues:")
	fmt.Println("1. Different handling of opcode detection")
	fmt.Println("2. Different interpretation of sign bit")
	fmt.Println("3. Bug in branch type determination")
}

// Analyze why branch targets differ
func analyzeTargetDifference(instr uint32, pc uint32) {
	fmt.Println("Analyzing branch target difference...")
	fmt.Printf("Base PC: 0x%08x\n", pc)

	opcode := instr & 0x7F

	if opcode == 0x63 { // BRANCH
		// Extract immediate field calculation
		imm12 := (instr >> 31) & 0x1
		imm11 := (instr >> 7) & 0x1
		imm10_5 := (instr >> 25) & 0x3F
		imm4_1 := (instr >> 8) & 0xF

		// Reconstruct the immediate value
		imm := (imm12 << 12) | (imm11 << 11) | (imm10_5 << 5) | (imm4_1 << 1)
		// Sign extend
		if imm12 > 0 {
			imm |= 0xFFFFE000
		}

		fmt.Printf("B-type immediate: 0x%x (%d)\n", imm, int32(imm))
		fmt.Printf("Expected target: 0x%08x\n", pc+imm)
	} else if opcode == 0x6F { // JAL
		// Extract immediate
		imm20 := (instr >> 31) & 0x1
		imm19_12 := (instr >> 12) & 0xFF
		imm11 := (instr >> 20) & 0x1
		imm10_1 := (instr >> 21) & 0x3FF

		// Reconstruct the immediate value
		imm := (imm20 << 20) | (imm19_12 << 12) | (imm11 << 11) | (imm10_1 << 1)
		// Sign extend
		if imm20 > 0 {
			imm |= 0xFFE00000
		}

		fmt.Printf("J-type immediate: 0x%x (%d)\n", imm, int32(imm))
		fmt.Printf("Expected target: 0x%08x\n", pc+imm)
	} else if opcode == 0x01 { // Compressed
		// Extract and process immediate based on compressed instruction format
		// ...
	}

	fmt.Println("\nPossible issues:")
	fmt.Println("1. Different immediate extraction/calculation")
	fmt.Println("2. Sign extension differences")
	fmt.Println("3. Incorrect bit field handling")
}
