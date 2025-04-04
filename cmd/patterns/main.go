package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"log"
	"os"
	"path/filepath"
	"strings"
	"time"
)

// OutputPair represents an output value pair from both simulators
type OutputPair struct {
	IVerilog  string `json:"iverilog"`
	Verilator string `json:"verilator"`
}

// MismatchInfo represents a generic mismatch between simulators
type MismatchInfo struct {
	ID        int                   `json:"id"`
	Inputs    map[string]string     `json:"inputs"`
	Outputs   map[string]OutputPair `json:"outputs"`
	Timestamp time.Time             `json:"timestamp"`
}

func main() {
	flag.Parse()

	// Collect all mismatch directories
	mismatchDir := "mismatches"
	files, err := os.ReadDir(mismatchDir)
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
	if err := os.WriteFile("mismatches.json", jsonData, 0644); err != nil {
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
		ID:        id,
		Inputs:    make(map[string]string),
		Outputs:   make(map[string]OutputPair),
		Timestamp: time.Now(),
	}

	// Find all input files
	inputFiles, err := filepath.Glob(filepath.Join(dirPath, "input_*.hex"))
	if err != nil || len(inputFiles) == 0 {
		return result, fmt.Errorf("no input files found in %s", dirPath)
	}

	// Process each input file
	for _, inputFile := range inputFiles {
		portName := strings.TrimPrefix(filepath.Base(inputFile), "input_")
		portName = strings.TrimSuffix(portName, ".hex")

		content, err := os.ReadFile(inputFile)
		if err != nil {
			return result, fmt.Errorf("failed to read input file %s: %v", inputFile, err)
		}

		result.Inputs[portName] = strings.TrimSpace(string(content))
	}

	// Find all IVerilog output files
	ivOutputFiles, err := filepath.Glob(filepath.Join(dirPath, "iv_*.hex"))
	if err != nil || len(ivOutputFiles) == 0 {
		return result, fmt.Errorf("no IVerilog output files found in %s", dirPath)
	}

	// Process each output file
	for _, ivFile := range ivOutputFiles {
		portName := strings.TrimPrefix(filepath.Base(ivFile), "iv_")
		portName = strings.TrimSuffix(portName, ".hex")

		// Find corresponding Verilator output
		vlFile := filepath.Join(dirPath, "vl_"+portName+".hex")
		if _, err := os.Stat(vlFile); os.IsNotExist(err) {
			continue // Skip if no corresponding Verilator file
		}

		// Read both outputs
		ivContent, err := os.ReadFile(ivFile)
		if err != nil {
			continue
		}

		vlContent, err := os.ReadFile(vlFile)
		if err != nil {
			continue
		}

		// Only add ports where outputs differ
		ivValue := strings.TrimSpace(string(ivContent))
		vlValue := strings.TrimSpace(string(vlContent))

		if ivValue != vlValue {
			result.Outputs[portName] = OutputPair{
				IVerilog:  ivValue,
				Verilator: vlValue,
			}
		}
	}

	if len(result.Outputs) == 0 {
		return result, fmt.Errorf("no mismatched outputs found in %s", dirPath)
	}

	return result, nil
}

// Analyze patterns in mismatches
func analyzePatterns(mismatches []MismatchInfo) {
	// Count mismatched outputs by port name
	portMismatchCounts := make(map[string]int)

	// Track patterns in input values
	inputPatterns := make(map[string]map[string]int)

	for _, m := range mismatches {
		// Count port-specific mismatches
		for portName := range m.Outputs {
			portMismatchCounts[portName]++
		}

		// Track patterns in inputs
		for portName, value := range m.Inputs {
			if _, exists := inputPatterns[portName]; !exists {
				inputPatterns[portName] = make(map[string]int)
			}
			inputPatterns[portName][value]++
		}
	}

	// Display results
	fmt.Println("\n=== Mismatch Patterns ===")

	// Most common mismatched outputs
	fmt.Println("\nMost frequently mismatched output ports:")
	for port, count := range portMismatchCounts {
		fmt.Printf("  %s: %d mismatches (%.1f%%)\n", port, count,
			float64(count)/float64(len(mismatches))*100)
	}

	// Most common input patterns associated with mismatches
	fmt.Println("\nCommon input patterns in mismatches:")
	for port, values := range inputPatterns {
		fmt.Printf("  Port %s:\n", port)

		// Find the top 3 most common values
		type valuePair struct {
			value string
			count int
		}
		pairs := make([]valuePair, 0)
		for val, count := range values {
			pairs = append(pairs, valuePair{val, count})
		}

		// Sort by frequency (simple bubble sort is fine for small lists)
		for i := 0; i < len(pairs)-1; i++ {
			for j := i + 1; j < len(pairs); j++ {
				if pairs[j].count > pairs[i].count {
					pairs[i], pairs[j] = pairs[j], pairs[i]
				}
			}
		}

		// Print top values (up to 3)
		limit := 3
		if len(pairs) < limit {
			limit = len(pairs)
		}

		for i := 0; i < limit; i++ {
			fmt.Printf("    Value '%s': %d occurrences (%.1f%%)\n",
				pairs[i].value, pairs[i].count,
				float64(pairs[i].count)/float64(len(mismatches))*100)
		}
	}
}
