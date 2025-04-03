package main

import (
	"flag"
	"fmt"
	"log"
	"os"
	"path/filepath"
	"strconv"
	"strings"

	"github.com/jns/pfuzz/internal/simulator"
	"github.com/jns/pfuzz/pkg/utils"
)

// Debug logger for both normal and debug messages
var debug *utils.DebugLogger

func main() {
	verbose := flag.Bool("v", false, "Verbose output")
	flag.Parse()

	// Initialize the debug logger
	debug = utils.NewDebugLogger(*verbose)

	// Check if we have a mismatch file to analyze
	args := flag.Args()
	if len(args) < 1 {
		fmt.Println("Usage: analyze [-v] <mismatch_file_or_dir> [--step]")
		os.Exit(1)
	}

	mismatchPath := args[0]
	stepMode := len(args) > 1 && args[1] == "--step"

	// Handle both directory and file formats
	isMismatchDir := false
	fileInfo, err := os.Stat(mismatchPath)
	if err != nil {
		log.Fatalf("Failed to access mismatch path: %v", err)
	}

	if fileInfo.IsDir() {
		isMismatchDir = true
		debug.Log("Analyzing mismatch directory: %s", mismatchPath)
	} else {
		debug.Log("Analyzing mismatch file: %s", mismatchPath)
	}

	var fetchRdata, fetchPc uint32
	var fetchValid uint8

	// Based on whether it's a directory or file, get the information differently
	if isMismatchDir {
		// Read data from the input files in the directory
		inputPath := filepath.Join(mismatchPath, "input.hex")
		pcPath := filepath.Join(mismatchPath, "pc.hex")
		validPath := filepath.Join(mismatchPath, "valid.hex")

		// Read instruction data
		inputContent, err := os.ReadFile(inputPath)
		if err != nil {
			log.Fatalf("Failed to read input file: %v", err)
		}
		pcContent, err := os.ReadFile(pcPath)
		if err != nil {
			log.Fatalf("Failed to read pc file: %v", err)
		}
		validContent, err := os.ReadFile(validPath)
		if err != nil {
			log.Fatalf("Failed to read valid file: %v", err)
		}

		// Parse the values
		fmt.Sscanf(string(inputContent), "%x", &fetchRdata)
		fmt.Sscanf(string(pcContent), "%x", &fetchPc)
		fetchValid = validContent[0] - '0'
	} else {
		// Original text file parsing
		content, err := os.ReadFile(mismatchPath)
		if err != nil {
			log.Fatalf("Failed to read mismatch file: %v", err)
		}

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
	}

	debug.Log("Analyzing mismatch with:")
	debug.Log("  Instruction: 0x%08x", fetchRdata)
	debug.Log("  PC: 0x%08x", fetchPc)
	debug.Log("  Valid: %d", fetchValid)

	// Decode the instruction
	debug.Log("Decoded instruction: %s\n", decodeInstruction(fetchRdata))

	// Create debug logs directory
	debugDir := "debug_logs"
	os.MkdirAll(debugDir, 0755)

	// Setup for simulation replay with debug output
	if err := utils.EnsureDirs(); err != nil {
		log.Fatal("Failed to create directories:", err)
	}

	// Create a separate directory for analysis
	analysisDir := filepath.Join(utils.TMP_DIR, "analysis")
	if err := os.MkdirAll(analysisDir, 0755); err != nil {
		log.Fatal("Failed to create analysis directory:", err)
	}

	// Write input files
	inputPath := filepath.Join(analysisDir, "input.hex")
	pcPath := filepath.Join(analysisDir, "pc.hex")
	validPath := filepath.Join(analysisDir, "valid.hex")
	ivTakenPath := filepath.Join(analysisDir, "iv_taken.hex")
	ivTargetPath := filepath.Join(analysisDir, "iv_target.hex")
	vlTakenPath := filepath.Join(analysisDir, "vl_taken.hex")
	vlTargetPath := filepath.Join(analysisDir, "vl_target.hex")

	if err := utils.WriteHexFile(inputPath, fetchRdata); err != nil {
		log.Fatal("Failed to write input file:", err)
	}
	if err := utils.WriteHexFile(pcPath, fetchPc); err != nil {
		log.Fatal("Failed to write PC file:", err)
	}
	if err := utils.WriteBinFile(validPath, fetchValid); err != nil {
		log.Fatal("Failed to write valid file:", err)
	}

	// If path is a directory, use the stored simulation results
	if isMismatchDir {
		debug.Log("Using saved simulation results from mismatch directory")

		// Read IVerilog results
		ivTakenPath := filepath.Join(mismatchPath, "iv_taken.hex")
		ivTargetPath := filepath.Join(mismatchPath, "iv_target.hex")
		ivTakenContent, err := os.ReadFile(ivTakenPath)
		if err != nil {
			log.Fatalf("Failed to read IVerilog taken file: %v", err)
		}
		ivTargetContent, err := os.ReadFile(ivTargetPath)
		if err != nil {
			log.Fatalf("Failed to read IVerilog target file: %v", err)
		}

		// Read Verilator results
		vlTakenPath := filepath.Join(mismatchPath, "vl_taken.hex")
		vlTargetPath := filepath.Join(mismatchPath, "vl_target.hex")
		vlTakenContent, err := os.ReadFile(vlTakenPath)
		if err != nil {
			log.Fatalf("Failed to read Verilator taken file: %v", err)
		}
		vlTargetContent, err := os.ReadFile(vlTargetPath)
		if err != nil {
			log.Fatalf("Failed to read Verilator target file: %v", err)
		}

		// Parse the results
		var ivResult, vlResult simulator.SimResult
		ivResult.BranchTaken = ivTakenContent[0] - '0'
		vlResult.BranchTaken = vlTakenContent[0] - '0'

		fmt.Sscanf(string(ivTargetContent), "%x", &ivResult.BranchPc)
		fmt.Sscanf(string(vlTargetContent), "%x", &vlResult.BranchPc)

		// Compare and display results
		debug.Log("\n=== Simulation Results (from saved files) ===")
		debug.Log("IVerilog: taken=%d pc=0x%08x", ivResult.BranchTaken, ivResult.BranchPc)
		debug.Log("Verilator: taken=%d pc=0x%08x", vlResult.BranchTaken, vlResult.BranchPc)

		if ivResult.BranchTaken != vlResult.BranchTaken {
			debug.Log("\n*** BRANCH TAKEN MISMATCH ***")
			analyzePredictionDifference(fetchRdata)
		}

		if ivResult.BranchPc != vlResult.BranchPc {
			debug.Log("\n*** BRANCH TARGET MISMATCH ***")
			debug.Log("PC difference: 0x%x", ivResult.BranchPc^vlResult.BranchPc)
			analyzeTargetDifference(fetchRdata, fetchPc)
		}

		return
	}

	// Add debug instrumentation to the Verilog files if in step mode
	if stepMode {
		// In step mode, modify the testbench to output detailed signals
		generateDebugTestbench()
	}

	// Update simulator creation to pass verbose flag
	ivSim := simulator.NewIVerilogSimulator(analysisDir, *verbose)
	vlSim := simulator.NewVerilatorSimulator(analysisDir)

	debug.Log("Running IVerilog simulation...")
	if err := ivSim.Compile(); err != nil {
		log.Fatal("Failed to compile IVerilog:", err)
	}
	if err := ivSim.RunTest(inputPath, pcPath, validPath, ivTakenPath, ivTargetPath); err != nil {
		log.Fatal("Failed to run IVerilog:", err)
	}
	ivResult, err := simulator.ReadSimResultsFromFiles(ivTakenPath, ivTargetPath)
	if err != nil {
		log.Fatal("Failed to read IVerilog results:", err)
	}

	debug.Log("Running Verilator simulation...")
	if err := vlSim.Compile(); err != nil {
		log.Fatal("Failed to compile Verilator:", err)
	}
	if err := vlSim.RunTest(inputPath, pcPath, validPath, vlTakenPath, vlTargetPath); err != nil {
		log.Fatal("Failed to run Verilator:", err)
	}
	vlResult, err := simulator.ReadSimResultsFromFiles(vlTakenPath, vlTargetPath)
	if err != nil {
		log.Fatal("Failed to read Verilator results:", err)
	}

	// Compare and display results
	debug.Log("\n=== Simulation Results ===")
	debug.Log("IVerilog: taken=%d pc=0x%08x", ivResult.BranchTaken, ivResult.BranchPc)
	debug.Log("Verilator: taken=%d pc=0x%08x", vlResult.BranchTaken, vlResult.BranchPc)

	if ivResult.BranchTaken != vlResult.BranchTaken {
		debug.Log("\n*** BRANCH TAKEN MISMATCH ***")
		analyzePredictionDifference(fetchRdata)
	}

	if ivResult.BranchPc != vlResult.BranchPc {
		debug.Log("\n*** BRANCH TARGET MISMATCH ***")
		debug.Log("PC difference: 0x%x", ivResult.BranchPc^vlResult.BranchPc)
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

	debug.Log("Analyzing branch prediction difference...")

	if opcode == 0x63 { // BRANCH
		funct3 := (instr >> 12) & 0x7
		imm12 := (instr >> 31) & 0x1
		debug.Log("Branch instruction with funct3=%d, sign bit=%d", funct3, imm12)
		debug.Log("Expected prediction: taken if sign bit is 1 (negative offset)")

		if imm12 == 1 {
			debug.Log("This branch should be predicted taken - check if simulators differ here")
		} else {
			debug.Log("This branch should be predicted not taken - check for bugs in condition")
		}
	} else if opcode == 0x6F { // JAL
		debug.Log("JAL instructions should always be predicted taken")
		debug.Log("Check if one simulator is incorrectly handling JAL cases")
	} else if opcode == 0x01 { // Compressed
		funct3 := (instr >> 13) & 0x7
		imm8 := (instr >> 12) & 0x1

		if funct3 == 0x5 || funct3 == 0x1 { // C.J or C.JAL
			debug.Log("Compressed jump should always be predicted taken")
		} else if funct3 == 0x6 || funct3 == 0x7 { // C.BEQZ or C.BNEZ
			debug.Log("Compressed branch with sign bit=%d", imm8)
			if imm8 == 1 {
				debug.Log("This compressed branch should be predicted taken - check if simulators differ")
			} else {
				debug.Log("This compressed branch should be predicted not taken - check for bugs")
			}
		}
	}

	debug.Log("\nPossible issues:")
	debug.Log("1. Different handling of opcode detection")
	debug.Log("2. Different interpretation of sign bit")
	debug.Log("3. Bug in branch type determination")
}

// Analyze why branch targets differ
func analyzeTargetDifference(instr uint32, pc uint32) {
	debug.Log("Analyzing branch target difference...")
	debug.Log("Base PC: 0x%08x", pc)

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

		debug.Log("B-type immediate: 0x%x (%d)", imm, int32(imm))
		debug.Log("Expected target: 0x%08x", pc+imm)
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

		debug.Log("J-type immediate: 0x%x (%d)", imm, int32(imm))
		debug.Log("Expected target: 0x%08x", pc+imm)
	} else if opcode == 0x01 { // Compressed
		// Extract and process immediate based on compressed instruction format
		// ...
	}

	debug.Log("\nPossible issues:")
	debug.Log("1. Different immediate extraction/calculation")
	debug.Log("2. Sign extension differences")
	debug.Log("3. Incorrect bit field handling")
}
