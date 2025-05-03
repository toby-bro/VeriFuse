package main

import (
	"flag"
	"fmt"
	"math/rand"
	"os"
	"path/filepath"
	"strings"

	"github.com/toby-bro/pfuzz/internal/simulator"
	"github.com/toby-bro/pfuzz/internal/verilog"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

func main() {
	verbose := flag.Bool("v", false, "Verbose output")
	verilogFile := flag.String("file", "", "Path to Verilog file (required)")
	moduleName := flag.String("module", "", "Module name (if different from filename)")
	mocked := flag.Bool("mocked", false, "Use mocked Verilog file")
	flag.Parse()

	debug := utils.NewDebugLogger(*verbose)

	// Check if file is provided
	if *verilogFile == "" {
		debug.Log("Error: No Verilog file specified. Use -file option.")
		os.Exit(1)
	}

	if err := utils.EnsureDirs(); err != nil {
		debug.Log("Failed to create directories: %v", err)
		os.Exit(1)
	}

	// Parse the Verilog file to get module information
	module, err := verilog.ParseVerilogFile(*verilogFile, *moduleName)
	if err != nil {
		debug.Log("Failed to parse Verilog file: %v", err)
		os.Exit(1)
	}

	if *mocked {
		module.Name = module.Name + "_mocked"
	}

	debug.Log("Using module: %s", module.Name)

	// Create a dedicated directory for focused tests
	focusedDir := filepath.Join(utils.TMP_DIR, "focused")
	if err := os.MkdirAll(focusedDir, 0755); err != nil {
		debug.Log("Failed to create focused directory: %v", err)
		os.Exit(1)
	}

	// Create generic test cases based on module inputs rather than hardcoded branch predictor tests
	// For each input port, create test cases with various values
	var testCases []struct {
		Name        string
		InputValues map[string]string
		Description string
	}

	// Build test cases dynamically based on module inputs
	for _, port := range module.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			// Create tests with different values for this input
			if port.Width == 1 {
				// For 1-bit ports, test both 0 and 1
				testCases = append(testCases, struct {
					Name        string
					InputValues map[string]string
					Description string
				}{
					Name:        port.Name + "_0",
					InputValues: map[string]string{port.Name: "0"},
					Description: fmt.Sprintf("Test %s with value 0", port.Name),
				})

				testCases = append(testCases, struct {
					Name        string
					InputValues map[string]string
					Description string
				}{
					Name:        port.Name + "_1",
					InputValues: map[string]string{port.Name: "1"},
					Description: fmt.Sprintf("Test %s with value 1", port.Name),
				})
			} else {
				// For multi-bit ports, test several interesting values with proper width
				testCases = append(testCases, struct {
					Name        string
					InputValues map[string]string
					Description string
				}{
					Name:        port.Name + "_zero",
					InputValues: map[string]string{port.Name: "0"},
					Description: fmt.Sprintf("Test %s with all zeros", port.Name),
				})

				// All ones - with proper hex width
				hexDigits := (port.Width + 3) / 4
				maxVal := strings.Repeat("f", hexDigits)
				testCases = append(testCases, struct {
					Name        string
					InputValues map[string]string
					Description string
				}{
					Name:        port.Name + "_max",
					InputValues: map[string]string{port.Name: maxVal},
					Description: fmt.Sprintf("Test %s with all ones", port.Name),
				})

				// Random value with proper width
				randValue := fmt.Sprintf("%0*x", hexDigits, rand.Uint64()%(1<<port.Width))
				testCases = append(testCases, struct {
					Name        string
					InputValues map[string]string
					Description string
				}{
					Name:        port.Name + "_random",
					InputValues: map[string]string{port.Name: randValue},
					Description: fmt.Sprintf("Test %s with random value 0x%s", port.Name, randValue),
				})

				// Single bit set (e.g. 0x00000004)
				bitPos := rand.Intn(port.Width)
				// Only create this test if the bit position is less than 64 (max uint64 size)
				if bitPos < 64 {
					bitVal := uint64(1) << uint(bitPos)
					singleBitVal := fmt.Sprintf("%0*x", hexDigits, bitVal)
					testCases = append(testCases, struct {
						Name        string
						InputValues map[string]string
						Description string
					}{
						Name:        fmt.Sprintf("%s_bit%d", port.Name, bitPos),
						InputValues: map[string]string{port.Name: singleBitVal},
						Description: fmt.Sprintf("Test %s with only bit %d set (0x%s)", port.Name, bitPos, singleBitVal),
					})
				}
			}
		}
	}

	// Prepare simulators with module name from file
	ivSim := simulator.NewIVerilogSimulator(focusedDir, *verbose)
	vlSim := simulator.NewVerilatorSimulator(focusedDir, module.Name)

	if err := ivSim.Compile(); err != nil {
		debug.Log("Failed to compile IVerilog: %v", err)
		os.Exit(1)
	}

	if err := vlSim.Compile(); err != nil {
		debug.Log("Failed to compile Verilator: %v", err)
		os.Exit(1)
	}

	// Run all test cases
	debug.Log("Running focused test cases...")
	for i, tc := range testCases {
		debug.Log("\n=== Test case: %s ===", tc.Name)
		debug.Log("Description: %s", tc.Description)

		// Create test-specific files
		testCaseDir := filepath.Join(focusedDir, fmt.Sprintf("case_%d_%s", i, tc.Name))
		if err := os.MkdirAll(testCaseDir, 0755); err != nil {
			debug.Log("Failed to create test case directory: %v", err)
			continue
		}

		// Write input files dynamically
		for portName, value := range tc.InputValues {
			inputPath := filepath.Join(testCaseDir, fmt.Sprintf("input_%s.hex", portName))
			if err := os.WriteFile(inputPath, []byte(value), 0644); err != nil {
				debug.Log("Failed to write input file for %s: %v", portName, err)
				continue
			}
		}

		// Create output paths dynamically
		ivOutputPaths := make(map[string]string)
		vlOutputPaths := make(map[string]string)

		for _, port := range module.Ports {
			if port.Direction == verilog.OUTPUT {
				ivOutputPaths[port.Name] = filepath.Join(testCaseDir, fmt.Sprintf("iv_%s.hex", port.Name))
				vlOutputPaths[port.Name] = filepath.Join(testCaseDir, fmt.Sprintf("vl_%s.hex", port.Name))
			}
		}

		// Run simulations with dynamic output paths
		if err := ivSim.RunTest(testCaseDir, ivOutputPaths); err != nil {
			debug.Log("IVerilog simulation failed: %v", err)
			continue
		}

		if err := vlSim.RunTest(testCaseDir, vlOutputPaths); err != nil {
			debug.Log("Verilator simulation failed: %v", err)
			continue
		}

		// Compare results generically, for each output port
		mismatch := false
		for portName, ivPath := range ivOutputPaths {
			vlPath := vlOutputPaths[portName]

			ivContent, err := os.ReadFile(ivPath)
			if err != nil {
				debug.Log("Failed to read IVerilog output for %s: %v", portName, err)
				continue
			}

			vlContent, err := os.ReadFile(vlPath)
			if err != nil {
				debug.Log("Failed to read Verilator output for %s: %v", portName, err)
				continue
			}

			ivValue := strings.TrimSpace(string(ivContent))
			vlValue := strings.TrimSpace(string(vlContent))

			debug.Log("Port %s: IVerilog=%s, Verilator=%s", portName, ivValue, vlValue)

			if ivValue != vlValue {
				debug.Log("MISMATCH DETECTED IN PORT %s", portName)
				mismatch = true
			}
		}

		// Create mismatch directory if needed
		if mismatch {
			mismatchDir := filepath.Join(utils.MISMATCHES_DIR, "focused_"+tc.Name)
			os.MkdirAll(mismatchDir, 0755)

			for portName := range tc.InputValues {
				inputPath := filepath.Join(testCaseDir, fmt.Sprintf("input_%s.hex", portName))
				utils.CopyFile(inputPath, filepath.Join(mismatchDir, fmt.Sprintf("input_%s.hex", portName)))
			}

			for portName := range ivOutputPaths {
				ivPath := ivOutputPaths[portName]
				vlPath := vlOutputPaths[portName]
				utils.CopyFile(ivPath, filepath.Join(mismatchDir, fmt.Sprintf("iv_%s.hex", portName)))
				utils.CopyFile(vlPath, filepath.Join(mismatchDir, fmt.Sprintf("vl_%s.hex", portName)))
			}

			// Also create a summary file
			summaryPath := filepath.Join(utils.MISMATCHES_DIR, fmt.Sprintf("focused_%s.txt", tc.Name))
			file, err := os.Create(summaryPath)
			if err == nil {
				fmt.Fprintf(file, "Focused test case: %s\n", tc.Name)
				fmt.Fprintf(file, "Description: %s\n\n", tc.Description)
				fmt.Fprintf(file, "Inputs:\n")
				for portName, value := range tc.InputValues {
					fmt.Fprintf(file, "  %s=%s\n", portName, value)
				}
				fmt.Fprintf(file, "\nResults:\n")
				for portName := range ivOutputPaths {
					ivPath := ivOutputPaths[portName]
					vlPath := vlOutputPaths[portName]
					ivContent, _ := os.ReadFile(ivPath)
					vlContent, _ := os.ReadFile(vlPath)
					fmt.Fprintf(file, "  Port %s: IVerilog=%s, Verilator=%s\n",
						portName, strings.TrimSpace(string(ivContent)), strings.TrimSpace(string(vlContent)))
				}
				file.Close()
			}
		} else {
			debug.Log("Results match")
		}
	}
}
