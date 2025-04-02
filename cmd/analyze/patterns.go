package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"io/ioutil"
	"log"
	"os"
	"path/filepath"
	"strings"
)

type MismatchInfo struct {
	ID             int    `json:"id"`
	Instruction    uint32 `json:"instruction"`
	PC             uint32 `json:"pc"`
	Valid          uint8  `json:"valid"`
	IVerilogTaken  uint8  `json:"iverilog_taken"`
	VerilatorTaken uint8  `json:"verilator_taken"`
	IVerilogPC     uint32 `json:"iverilog_pc"`
	VerilatorPC    uint32 `json:"verilator_pc"`
	OpcodeType     string `json:"opcode_type"`
}

func main() {
	flag.Parse()

	// Collect all mismatch directories
	mismatchDir := "mismatches"
	files, err := ioutil.ReadDir(mismatchDir)
	if err != nil {
		log.Fatalf("Failed to read mismatches directory: %v", err)
	}

	var mismatches []MismatchInfo
	for _, file := range files {
		if !strings.HasPrefix(file.Name(), "mismatch_") {
			continue
		}

		// Check if it's a directory containing test data
		dirPath := filepath.Join(mismatchDir, file.Name())
		fileInfo, err := os.Stat(dirPath)
		if err != nil || !fileInfo.IsDir() {
			// Skip if not a directory
			continue
		}

		// Process mismatch directory
		mismatch, err := parseMismatchDir(dirPath, file.Name())
		if err != nil {
			log.Printf("Failed to process directory %s: %v", file.Name(), err)
			continue
		}

		mismatches = append(mismatches, mismatch)
	}

	if len(mismatches) == 0 {
		log.Fatal("No mismatch directories found. Run the fuzzer first to generate mismatches.")
	}

	// Export as JSON for further analysis
	jsonData, err := json.MarshalIndent(mismatches, "", "  ")
	if err != nil {
		log.Fatalf("Failed to convert to JSON: %v", err)
	}
	if err := ioutil.WriteFile("mismatches.json", jsonData, 0644); err != nil {
		log.Fatalf("Failed to write JSON file: %v", err)
	}
	fmt.Println("Exported all mismatch data to mismatches.json")

	// Analyze patterns
	fmt.Printf("Found %d mismatches\n", len(mismatches))
	analyzePatterns(mismatches)
}

// Parse a mismatch directory into structured data
func parseMismatchDir(dirPath, dirName string) (MismatchInfo, error) {
	// Extract the test case ID from filename
	var id int
	fmt.Sscanf(dirName, "mismatch_%d", &id)

	// Initialize the mismatch info
	result := MismatchInfo{
		ID: id,
	}

	// Read input files
	inputPath := filepath.Join(dirPath, "input.hex")
	pcPath := filepath.Join(dirPath, "pc.hex")
	validPath := filepath.Join(dirPath, "valid.hex")

	// Read IVerilog result files
	ivTakenPath := filepath.Join(dirPath, "iv_taken.hex")
	ivTargetPath := filepath.Join(dirPath, "iv_target.hex")

	// Read Verilator result files
	vlTakenPath := filepath.Join(dirPath, "vl_taken.hex")
	vlTargetPath := filepath.Join(dirPath, "vl_target.hex")

	// Check if all files exist
	requiredFiles := []string{inputPath, pcPath, validPath, ivTakenPath, ivTargetPath, vlTakenPath, vlTargetPath}
	for _, filePath := range requiredFiles {
		if _, err := os.Stat(filePath); os.IsNotExist(err) {
			return result, fmt.Errorf("missing required file: %s", filePath)
		}
	}

	// Read input data
	inputContent, err := os.ReadFile(inputPath)
	if err != nil {
		return result, err
	}
	pcContent, err := os.ReadFile(pcPath)
	if err != nil {
		return result, err
	}
	validContent, err := os.ReadFile(validPath)
	if err != nil {
		return result, err
	}

	// Parse input values
	fmt.Sscanf(string(inputContent), "%x", &result.Instruction)
	fmt.Sscanf(string(pcContent), "%x", &result.PC)
	result.Valid = validContent[0] - '0'

	// Read IVerilog results
	ivTakenContent, _ := os.ReadFile(ivTakenPath)
	ivTargetContent, _ := os.ReadFile(ivTargetPath)

	// Read Verilator results
	vlTakenContent, _ := os.ReadFile(vlTakenPath)
	vlTargetContent, _ := os.ReadFile(vlTargetPath)

	// Parse simulator results
	result.IVerilogTaken = ivTakenContent[0] - '0'
	result.VerilatorTaken = vlTakenContent[0] - '0'
	fmt.Sscanf(string(ivTargetContent), "%x", &result.IVerilogPC)
	fmt.Sscanf(string(vlTargetContent), "%x", &result.VerilatorPC)

	// Determine opcode type
	opcode := result.Instruction & 0x7F
	switch opcode {
	case 0x63:
		result.OpcodeType = "BRANCH"
	case 0x6F:
		result.OpcodeType = "JAL"
	case 0x01:
		result.OpcodeType = "COMPRESSED"
	default:
		result.OpcodeType = "OTHER"
	}

	return result, nil
}

// Analyze patterns in mismatches
func analyzePatterns(mismatches []MismatchInfo) {
	// Count by opcode type
	opcodeStats := make(map[string]int)

	// Track branch taken vs. not taken discrepancies
	takenMismatches := 0

	// Track PC mismatches
	pcMismatches := 0

	// Track bit patterns
	opcodePatterns := make(map[uint32]int)

	for _, m := range mismatches {
		opcodeStats[m.OpcodeType]++

		if m.IVerilogTaken != m.VerilatorTaken {
			takenMismatches++
		}

		if m.IVerilogPC != m.VerilatorPC {
			pcMismatches++
		}

		// Track the opcode byte
		opcodeByte := m.Instruction & 0x7F
		opcodePatterns[opcodeByte]++
	}

	// Display results
	fmt.Println("\n=== Mismatch Patterns ===")
	fmt.Printf("Branch taken mismatches: %d (%.1f%%)\n", takenMismatches,
		float64(takenMismatches)/float64(len(mismatches))*100)
	fmt.Printf("Branch target mismatches: %d (%.1f%%)\n", pcMismatches,
		float64(pcMismatches)/float64(len(mismatches))*100)

	fmt.Println("\nOpcode distribution:")
	for opcode, count := range opcodeStats {
		fmt.Printf("  %s: %d (%.1f%%)\n", opcode, count,
			float64(count)/float64(len(mismatches))*100)
	}

	fmt.Println("\nMost common opcode bytes:")
	for opcode, count := range opcodePatterns {
		if count > 1 {
			fmt.Printf("  0x%02x: %d occurrences\n", opcode, count)
		}
	}
}
