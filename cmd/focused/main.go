package main

import (
	"errors"
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

type config struct {
	verbose     int
	verilogFile string
	moduleName  string
	mocked      bool
}

type testCase struct {
	Name        string
	InputValues map[string]string
	Description string
}

func parseFlags() (*config, error) {
	cfg := &config{}
	vFlag := flag.Bool(
		"v",
		false,
		"Verbose output (level 1). Higher levels (-vv, -vvv) take precedence.",
	)
	vvFlag := flag.Bool(
		"vv",
		false,
		"Verbose output (level 2). Higher level (-vvv) takes precedence.",
	)
	vvvFlag := flag.Bool("vvv", false, "Verbose output (level 3).")
	flag.StringVar(&cfg.verilogFile, "file", "", "Path to Verilog file (required)")
	flag.StringVar(&cfg.moduleName, "module", "", "Module name (if different from filename)")
	flag.BoolVar(&cfg.mocked, "mocked", false, "Use mocked Verilog file")
	flag.Parse()
	var verboseLevel int
	switch {
	case *vvvFlag:
		verboseLevel = 4
	case *vvFlag:
		verboseLevel = 3
	case *vFlag:
		verboseLevel = 2
	default:
		verboseLevel = 1
	}

	cfg.verbose = verboseLevel

	if cfg.verilogFile == "" {
		return nil, errors.New("no Verilog file specified. Use -file option")
	}
	return cfg, nil
}

func setupEnvironment(cfg *config, debug *utils.DebugLogger) (*verilog.Module, string, error) {
	if err := utils.EnsureDirs(); err != nil {
		return nil, "", fmt.Errorf("failed to create directories: %w", err)
	}

	// Parse the Verilog file to get module information
	module, err := verilog.ParseVerilogFile(cfg.verilogFile, cfg.moduleName)
	if err != nil {
		return nil, "", fmt.Errorf("failed to parse Verilog file: %w", err)
	}

	if cfg.mocked {
		module.Name += "_mocked"
	}
	debug.Info("Using module: %s", module.Name)

	// Create a dedicated directory for focused tests
	focusedDir := filepath.Join(utils.TMP_DIR, "focused")
	if err := os.MkdirAll(focusedDir, 0o755); err != nil {
		return nil, "", fmt.Errorf("failed to create focused directory: %w", err)
	}

	return module, focusedDir, nil
}

func generateTestCases(module *verilog.Module) ([]testCase, error) {
	var testCases []testCase
	// Build test cases dynamically based on module inputs
	for _, port := range module.Ports {
		if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
			// Create tests with different values for this input
			if port.Width == 1 {
				// For 1-bit ports, test both 0 and 1
				testCases = append(testCases, testCase{
					Name:        port.Name + "_0",
					InputValues: map[string]string{port.Name: "0"},
					Description: fmt.Sprintf("Test %s with value 0", port.Name),
				})
				testCases = append(testCases, testCase{
					Name:        port.Name + "_1",
					InputValues: map[string]string{port.Name: "1"},
					Description: fmt.Sprintf("Test %s with value 1", port.Name),
				})
			} else {
				hexDigits := (port.Width + 3) / 4
				// Test zero
				testCases = append(testCases, testCase{
					Name:        port.Name + "_zero",
					InputValues: map[string]string{port.Name: "0"},
					Description: fmt.Sprintf("Test %s with all zeros", port.Name),
				})

				// Test max value
				maxVal := strings.Repeat("f", hexDigits)
				// Trim leading 'f's if width is not a multiple of 4
				if port.Width%4 != 0 {
					mask := (uint64(1) << port.Width) - 1
					maxValNum := uint64(0)
					n, err := fmt.Sscan("0x"+maxVal, &maxValNum)
					if err != nil || n != 1 {
						return nil, fmt.Errorf("failed to parse max value: %w", err)
					}
					maxVal = fmt.Sprintf("%0*x", hexDigits, maxValNum&mask)
				}
				testCases = append(testCases, testCase{
					Name:        port.Name + "_max",
					InputValues: map[string]string{port.Name: maxVal},
					Description: fmt.Sprintf("Test %s with all ones (0x%s)", port.Name, maxVal),
				})

				// Test random value
				randValNum := rand.Uint64()
				if port.Width < 64 {
					randValNum %= (1 << port.Width)
				}
				randValue := fmt.Sprintf("%0*x", hexDigits, randValNum)
				testCases = append(testCases, testCase{
					Name:        port.Name + "_random",
					InputValues: map[string]string{port.Name: randValue},
					Description: fmt.Sprintf("Test %s with random value 0x%s", port.Name, randValue),
				})

				// Test single bit set
				bitPos := rand.Intn(port.Width)
				if bitPos < 64 { // Ensure bitPos fits within uint64 for shifting
					bitVal := uint64(1) << uint(bitPos)
					singleBitVal := fmt.Sprintf("%0*x", hexDigits, bitVal)
					testCases = append(testCases, testCase{
						Name:        fmt.Sprintf("%s_bit%d", port.Name, bitPos),
						InputValues: map[string]string{port.Name: singleBitVal},
						Description: fmt.Sprintf("Test %s with only bit %d set (0x%s)", port.Name, bitPos, singleBitVal),
					})
				}
			}
		}
	}
	return testCases, nil
}

func compileSimulators(
	baseDir, moduleName string,
	verbose int,
	debug *utils.DebugLogger,
) (simulator.Simulator, simulator.Simulator, error) {
	ivSim := simulator.NewIVerilogSimulator(baseDir, verbose)
	vlSim := simulator.NewVerilatorSimulator(baseDir, moduleName, true, verbose)

	if err := ivSim.Compile(); err != nil {
		return nil, nil, fmt.Errorf("failed to compile IVerilog: %w", err)
	}
	debug.Info("IVerilog compiled successfully.")

	if err := vlSim.Compile(); err != nil {
		return nil, nil, fmt.Errorf("failed to compile Verilator: %w", err)
	}
	debug.Info("Verilator compiled successfully.")

	return ivSim, vlSim, nil
}

func runAndCompareTestCase(
	tc testCase,
	module *verilog.Module,
	ivSim, vlSim simulator.Simulator,
	baseDir string,
	debug *utils.DebugLogger,
	caseIndex int,
) error {
	debug.Info("\n=== Test case: %s ===", tc.Name)
	debug.Info("Description: %s", tc.Description)

	// Create test-specific directory
	testCaseDir := filepath.Join(baseDir, fmt.Sprintf("case_%d_%s", caseIndex, tc.Name))
	if err := os.MkdirAll(testCaseDir, 0o755); err != nil {
		return fmt.Errorf("failed to create test case directory %s: %w", testCaseDir, err)
	}

	// Write input files
	inputPaths := make(map[string]string)
	for portName, value := range tc.InputValues {
		inputPath := filepath.Join(testCaseDir, fmt.Sprintf("input_%s.hex", portName))
		if err := os.WriteFile(inputPath, []byte(value), 0o644); err != nil {
			return fmt.Errorf("failed to write input file for %s: %w", portName, err)
		}
		inputPaths[portName] = inputPath
	}

	// Prepare output paths
	ivOutputPaths := make(map[string]string)
	vlOutputPaths := make(map[string]string)
	for _, port := range module.Ports {
		if port.Direction == verilog.OUTPUT ||
			port.Direction == verilog.INOUT { // Also capture INOUT as output
			ivOutputPaths[port.Name] = filepath.Join(
				testCaseDir,
				fmt.Sprintf("iv_%s.hex", port.Name),
			)
			vlOutputPaths[port.Name] = filepath.Join(
				testCaseDir,
				fmt.Sprintf("vl_%s.hex", port.Name),
			)
		}
	}

	// Run simulations
	if err := ivSim.RunTest(testCaseDir, ivOutputPaths); err != nil {
		return fmt.Errorf("IVerilog simulation failed: %w", err)
	}
	if err := vlSim.RunTest(testCaseDir, vlOutputPaths); err != nil {
		return fmt.Errorf("Verilator simulation failed: %w", err)
	}

	// Compare results
	mismatch := false
	results := make(map[string][2]string) // portName -> [ivValue, vlValue]

	for portName, ivPath := range ivOutputPaths {
		vlPath := vlOutputPaths[portName]

		ivContent, err := os.ReadFile(ivPath)
		if err != nil {
			debug.Info("Warning: Failed to read IVerilog output for %s: %v", portName, err)
			// Continue comparison with empty string or handle error differently?
			ivContent = []byte{}
		}
		vlContent, err := os.ReadFile(vlPath)
		if err != nil {
			debug.Info("Warning: Failed to read Verilator output for %s: %v", portName, err)
			vlContent = []byte{}
		}

		ivValue := strings.TrimSpace(string(ivContent))
		vlValue := strings.TrimSpace(string(vlContent))
		results[portName] = [2]string{ivValue, vlValue}

		debug.Info("Port %s: IVerilog=%s, Verilator=%s", portName, ivValue, vlValue)

		if ivValue != vlValue {
			debug.Info("MISMATCH DETECTED IN PORT %s", portName)
			mismatch = true
		}
	}

	if mismatch {
		if err := handleMismatch(tc, inputPaths, ivOutputPaths, vlOutputPaths, results, debug); err != nil {
			debug.Info("Error handling mismatch: %v", err) // Log error but continue
		}
	} else {
		debug.Info("Results match")
	}

	return nil // Indicate successful run and comparison for this test case
}

func handleMismatch(
	tc testCase,
	inputPaths map[string]string,
	ivOutputPaths map[string]string,
	vlOutputPaths map[string]string,
	results map[string][2]string,
	debug *utils.DebugLogger,
) error {
	mismatchDir := filepath.Join(utils.MISMATCHES_DIR, "focused_"+tc.Name)
	if err := os.MkdirAll(mismatchDir, 0o755); err != nil {
		return fmt.Errorf("failed to create mismatch directory %s: %w", mismatchDir, err)
	}

	// Copy input files
	for portName, srcPath := range inputPaths {
		destPath := filepath.Join(mismatchDir, fmt.Sprintf("input_%s.hex", portName))
		if err := utils.CopyFile(srcPath, destPath); err != nil {
			debug.Info("Warning: Failed to copy input file %s: %v", srcPath, err)
			// Continue copying other files
		}
	}

	// Copy output files
	for portName, ivPath := range ivOutputPaths {
		vlPath := vlOutputPaths[portName]
		ivDest := filepath.Join(mismatchDir, fmt.Sprintf("iv_%s.hex", portName))
		vlDest := filepath.Join(mismatchDir, fmt.Sprintf("vl_%s.hex", portName))

		if err := utils.CopyFile(ivPath, ivDest); err != nil {
			debug.Info("Warning: Failed to copy IVerilog output for %s: %v", portName, err)
		}
		if err := utils.CopyFile(vlPath, vlDest); err != nil {
			debug.Info("Warning: Failed to copy Verilator output for %s: %v", portName, err)
		}
	}

	// Create summary file
	summaryPath := filepath.Join(
		utils.MISMATCHES_DIR,
		fmt.Sprintf("focused_%s_summary.txt", tc.Name),
	)
	file, err := os.Create(summaryPath)
	if err != nil {
		return fmt.Errorf("failed to create summary file %s: %w", summaryPath, err)
	}
	defer file.Close()

	fmt.Fprintf(file, "Focused Test Case Mismatch Report\n")
	fmt.Fprintf(file, "=================================\n")
	fmt.Fprintf(file, "Test Case Name: %s\n", tc.Name)
	fmt.Fprintf(file, "Description: %s\n\n", tc.Description)
	fmt.Fprintf(file, "Inputs:\n")
	for portName, value := range tc.InputValues {
		fmt.Fprintf(file, "  %s = %s\n", portName, value)
	}
	fmt.Fprintf(file, "\nOutputs (Mismatch Detected):\n")
	for portName, values := range results {
		ivVal, vlVal := values[0], values[1]
		status := "Match"
		if ivVal != vlVal {
			status = "MISMATCH"
		}
		fmt.Fprintf(file, "  Port %s:\n", portName)
		fmt.Fprintf(file, "    IVerilog:  %s\n", ivVal)
		fmt.Fprintf(file, "    Verilator: %s\n", vlVal)
		fmt.Fprintf(file, "    Status:    %s\n", status)
	}
	debug.Info("Mismatch details saved to %s and directory %s", summaryPath, mismatchDir)
	return nil
}

func main() {
	cfg, err := parseFlags()
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}

	debug := utils.NewDebugLogger(cfg.verbose)

	module, focusedDir, err := setupEnvironment(cfg, debug)
	if err != nil {
		debug.Info("Environment setup failed: %v", err)
		os.Exit(1)
	}

	testCases, err := generateTestCases(module)
	if err != nil {
		debug.Info("Test case generation failed: %v", err)
		os.Exit(1)
	}
	if len(testCases) == 0 {
		debug.Info("No test cases generated. Check module inputs.")
		os.Exit(0) // Not necessarily an error, maybe no inputs?
	}
	debug.Info("Generated %d test cases.", len(testCases))

	ivSim, vlSim, err := compileSimulators(focusedDir, module.Name, cfg.verbose, debug)
	if err != nil {
		debug.Info("Simulator compilation failed: %v", err)
		os.Exit(1)
	}

	debug.Info("Running focused test cases...")
	var runErrors []error
	for i, tc := range testCases {
		err := runAndCompareTestCase(tc, module, ivSim, vlSim, focusedDir, debug, i)
		if err != nil {
			debug.Info("Error running test case %s: %v", tc.Name, err)
			runErrors = append(runErrors, fmt.Errorf("case %s: %w", tc.Name, err))
			// Decide whether to continue or stop on first error
			// For now, continue to run all tests
		}
	}

	if len(runErrors) > 0 {
		debug.Info("\n--- Summary of Errors ---")
		for _, runErr := range runErrors {
			debug.Info("- %v", runErr)
		}
		os.Exit(1) // Indicate that some tests failed
	}

	debug.Info("\nAll focused test cases completed.")
}
