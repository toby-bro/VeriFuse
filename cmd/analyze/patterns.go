package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"io/ioutil"
	"log"
	"path/filepath"
	"strconv"
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

	// Collect all mismatch files
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

		data, err := ioutil.ReadFile(filepath.Join(mismatchDir, file.Name()))
		if err != nil {
			log.Printf("Failed to read %s: %v", file.Name(), err)
			continue
		}

		mismatch := parseMismatchFile(string(data), file.Name())
		mismatches = append(mismatches, mismatch)
	}

	if len(mismatches) == 0 {
		log.Fatal("No mismatch files found")
	}

	// Export as JSON for further analysis
	jsonData, err := json.MarshalIndent(mismatches, "", "  ")
	if err != nil {
		log.Fatalf("Failed to convert to JSON: %v", err)
	}
	if err := ioutil.WriteFile("mismatches.json", jsonData, 0644); err != nil {
		log.Fatalf("Failed to write JSON file: %v", err)
	}

	// Analyze patterns
	fmt.Printf("Found %d mismatches\n", len(mismatches))
	analyzePatterns(mismatches)
}

// Parse a mismatch file into structured data
func parseMismatchFile(content string, filename string) MismatchInfo {
	// Extract the test case ID from filename
	var id int
	fmt.Sscanf(filename, "mismatch_%d.txt", &id)

	// Initialize the mismatch info
	result := MismatchInfo{
		ID: id,
	}

	// Parse the content line by line
	lines := strings.Split(content, "\n")
	for i, line := range lines {
		line = strings.TrimSpace(line)

		// Extract instruction details
		if strings.HasPrefix(line, "rdata=0x") {
			val, _ := strconv.ParseUint(strings.TrimPrefix(line, "rdata=0x"), 16, 32)
			result.Instruction = uint32(val)
		} else if strings.HasPrefix(line, "pc=0x") {
			val, _ := strconv.ParseUint(strings.TrimPrefix(line, "pc=0x"), 16, 32)
			result.PC = uint32(val)
		} else if strings.HasPrefix(line, "valid=") {
			val, _ := strconv.ParseUint(strings.TrimPrefix(line, "valid="), 10, 8)
			result.Valid = uint8(val)
		}

		// Extract simulation results
		if strings.Contains(line, "IVerilog: taken=") {
			fmt.Sscanf(line, "  IVerilog: taken=%d pc=0x%x",
				&result.IVerilogTaken, &result.IVerilogPC)
		} else if strings.Contains(line, "Verilator: taken=") {
			fmt.Sscanf(line, "  Verilator: taken=%d pc=0x%x",
				&result.VerilatorTaken, &result.VerilatorPC)
		}

		// Try to determine opcode type
		if i == 0 && strings.Contains(line, "Decoded:") {
			if strings.Contains(line, "BRANCH") {
				result.OpcodeType = "BRANCH"
			} else if strings.Contains(line, "JAL") {
				result.OpcodeType = "JAL"
			} else if strings.Contains(line, "C.") {
				result.OpcodeType = "COMPRESSED"
			} else {
				result.OpcodeType = "OTHER"
			}
		}
	}

	// Determine opcode type if not already set
	if result.OpcodeType == "" {
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
	}

	return result
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
