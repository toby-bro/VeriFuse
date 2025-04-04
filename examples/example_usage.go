package main

import (
	"fmt"
	"os"
	"path/filepath"

	"github.com/jns/pfuzz/pkg/utils"
)

func main() {
	// Example usage for different verilog modules
	examples := []struct {
		name        string
		modulePath  string
		moduleName  string
		description string
		numTests    int
		strategy    string
	}{
		{
			name:        "ibex_branch_predictor",
			modulePath:  "/home/jns/Documents/Berkeley/pfuzz/ibex_branch_predict.sv",
			moduleName:  "ibex_branch_predict",
			description: "Branch predictor from the Ibex RISC-V core",
			numTests:    100,
			strategy:    "random",
		},
		// Add more examples here as needed
	}

	for _, example := range examples {
		fmt.Printf("\n=== Running example: %s ===\n", example.name)
		fmt.Printf("Description: %s\n", example.description)

		// Create command arguments
		args := []string{
			"-file", example.modulePath,
		}

		if example.moduleName != "" {
			args = append(args, "-module", example.moduleName)
		}

		args = append(args,
			"-n", fmt.Sprintf("%d", example.numTests),
			"-strategy", example.strategy,
			"-workers", "2",
			"-v",
		)

		// Build command string
		cmdStr := fmt.Sprintf("pfuzz %s", utils.JoinStrings(args, " "))
		fmt.Printf("Running command: %s\n\n", cmdStr)

		// In a real script, you would execute this command
		// For this example, we just print it
	}
}

// Save example results to a file for later review
func saveResults(example string, outputDir string) error {
	resultsDir := filepath.Join("examples", "results", example)
	if err := os.MkdirAll(resultsDir, 0755); err != nil {
		return fmt.Errorf("failed to create results directory: %v", err)
	}

	// Copy mismatches to results directory
	mismatchesDir := filepath.Join("mismatches")
	if _, err := os.Stat(mismatchesDir); err == nil {
		entries, err := os.ReadDir(mismatchesDir)
		if err != nil {
			return fmt.Errorf("failed to read mismatches directory: %v", err)
		}

		for _, entry := range entries {
			srcPath := filepath.Join(mismatchesDir, entry.Name())
			dstPath := filepath.Join(resultsDir, entry.Name())

			// Copy file or directory
			if entry.IsDir() {
				if err := utils.CopyDir(srcPath, dstPath); err != nil {
					return fmt.Errorf("failed to copy mismatch directory: %v", err)
				}
			} else {
				if err := utils.CopyFile(srcPath, dstPath); err != nil {
					return fmt.Errorf("failed to copy mismatch file: %v", err)
				}
			}
		}
	}

	return nil
}
