package main

import (
	"flag"
	"fmt"
	"log"
	"os"
	"path/filepath"
	"strings"

	"github.com/toby-bro/pfuzz/internal/simulator"
	"github.com/toby-bro/pfuzz/internal/testgen"
	"github.com/toby-bro/pfuzz/internal/verilog"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

// Debug logger for both normal and debug messages
var debug *utils.DebugLogger

// setupAnalysisEnvironment creates necessary directories for analysis.
func setupAnalysisEnvironment() (string, error) {
	// Create debug logs directory
	debugDir := "debug_logs"
	if err := os.MkdirAll(debugDir, 0o755); err != nil {
		return "", fmt.Errorf("failed to create debug logs directory: %v", err)
	}

	// Setup for simulation replay with debug output
	if err := utils.EnsureDirs(); err != nil {
		return "", fmt.Errorf("failed to create tmp directories: %v", err)
	}

	// Create a separate directory for analysis
	analysisDir := filepath.Join(utils.TMP_DIR, "analysis")
	if err := os.MkdirAll(analysisDir, 0o755); err != nil {
		return "", fmt.Errorf("failed to create analysis directory: %v", err)
	}
	return analysisDir, nil
}

// getExecutedVerilogFile finds the relevant Verilog file in tmp_gen.
func getExecutedVerilogFile(mocked bool) string {
	tmpGen, err := os.ReadDir("tmp_gen")
	if err != nil {
		return ""
	}
	for _, file := range tmpGen {
		if (strings.HasSuffix(file.Name(), "_mocked.sv") && mocked) ||
			(strings.HasSuffix(file.Name(), ".sv") && !mocked && !strings.Contains(file.Name(), "testbench")) {
			return filepath.Join("tmp_gen", file.Name())
		}
	}
	return ""
}

// findAndPrepareVerilog finds, parses, and copies the Verilog file to the analysis directory.
func findAndPrepareVerilog(
	analysisDir, moduleName string,
	mocked bool,
	debug *utils.DebugLogger,
) (*verilog.Module, string, error) {
	verilogFile := getExecutedVerilogFile(mocked)
	if verilogFile == "" {
		return nil, "", fmt.Errorf("no Verilog file found in tmp_gen directory (mocked=%v)", mocked)
	}
	debug.Log("Found Verilog file: %s", verilogFile)

	module, err := verilog.ParseVerilogFile(verilogFile, moduleName)
	if err != nil {
		return nil, "", fmt.Errorf("failed to parse Verilog file %s: %v", verilogFile, err)
	}
	debug.Log("Using module: %s", module.Name)

	analysisVerilogFile := filepath.Join(analysisDir, filepath.Base(verilogFile))
	if err := utils.CopyFile(verilogFile, analysisVerilogFile); err != nil {
		return nil, "", fmt.Errorf("failed to copy Verilog file to analysis dir: %v", err)
	}
	debug.Log("Copied Verilog file to %s", analysisVerilogFile)

	return module, analysisVerilogFile, nil
}

// generateDebugTestbench creates testbenches with debug instrumentation in the analysis directory.
func generateDebugTestbench(
	module *verilog.Module,
	analysisDir string,
	debug *utils.DebugLogger,
) error {
	gen := testgen.NewGenerator(module)

	// Generate both the SystemVerilog and C++ testbenches in the default tmp dir first
	if err := gen.GenerateTestbenches(); err != nil {
		return fmt.Errorf("failed to generate debug testbenches: %v", err)
	}

	// Define source paths
	svTestbenchSrc := filepath.Join(utils.TMP_DIR, "testbench.sv")
	cppTestbenchSrc := filepath.Join(utils.TMP_DIR, "testbench.cpp")

	// Define destination paths
	svTestbenchDest := filepath.Join(analysisDir, "testbench.sv")
	cppTestbenchDest := filepath.Join(analysisDir, "testbench.cpp")

	// Copy testbenches to analysis directory
	if err := utils.CopyFile(svTestbenchSrc, svTestbenchDest); err != nil {
		return fmt.Errorf("failed to copy SV testbench to analysis dir: %v", err)
	}
	debug.Log("Copied SV testbench to %s", svTestbenchDest)

	if err := utils.CopyFile(cppTestbenchSrc, cppTestbenchDest); err != nil {
		return fmt.Errorf("failed to copy C++ testbench to analysis dir: %v", err)
	}
	debug.Log("Copied C++ testbench to %s", cppTestbenchDest)

	return nil
}

// prepareInputFiles copies input hex files from the mismatch directory to the analysis directory.
func prepareInputFiles(mismatchPath, analysisDir string, debug *utils.DebugLogger) error {
	inputFiles, err := filepath.Glob(filepath.Join(mismatchPath, "input_*.hex"))
	if err != nil {
		return fmt.Errorf("error finding input files in %s: %v", mismatchPath, err)
	}
	if len(inputFiles) == 0 {
		return fmt.Errorf(
			"no input files (input_*.hex) found in mismatch directory %s",
			mismatchPath,
		)
	}

	debug.Log("Found %d input files:", len(inputFiles))
	for _, f := range inputFiles {
		content, _ := os.ReadFile(f) // Error ignored for logging
		portName := strings.TrimPrefix(filepath.Base(f), "input_")
		portName = strings.TrimSuffix(portName, ".hex")
		debug.Log("  %s = %s", portName, strings.TrimSpace(string(content)))

		destPath := filepath.Join(analysisDir, filepath.Base(f))
		if err := utils.CopyFile(f, destPath); err != nil {
			return fmt.Errorf("failed to copy input file %s to analysis dir: %v", f, err)
		}
	}
	return nil
}

// setupAndCompileSimulators initializes and compiles IVerilog and Verilator simulators.
func setupAndCompileSimulators(
	analysisDir string,
	moduleName string,
	verbose bool,
	debug *utils.DebugLogger,
) (simulator.Simulator, simulator.Simulator, error) {
	ivSim := simulator.NewIVerilogSimulator(analysisDir, verbose)
	vlSim := simulator.NewVerilatorSimulator(analysisDir, moduleName, true)

	debug.Log("Compiling IVerilog simulator...")
	if err := ivSim.Compile(); err != nil {
		return nil, nil, fmt.Errorf("failed to compile IVerilog: %v", err)
	}

	debug.Log("Compiling Verilator simulator...")
	if err := vlSim.Compile(); err != nil {
		return nil, nil, fmt.Errorf("failed to compile Verilator: %v", err)
	}

	return ivSim, vlSim, nil
}

// runSimulations executes the compiled simulators and returns the output file paths.
func runSimulations(
	ivSim simulator.Simulator,
	vlSim simulator.Simulator,
	module *verilog.Module,
	analysisDir string,
	debug *utils.DebugLogger,
) (map[string]string, map[string]string, error) {
	ivOutputPaths := make(map[string]string)
	vlOutputPaths := make(map[string]string)

	for _, port := range module.Ports {
		if port.Direction == verilog.OUTPUT {
			ivOutputPaths[port.Name] = filepath.Join(
				analysisDir,
				fmt.Sprintf("iv_%s.hex", port.Name),
			)
			vlOutputPaths[port.Name] = filepath.Join(
				analysisDir,
				fmt.Sprintf("vl_%s.hex", port.Name),
			)
		}
	}

	debug.Log("Running IVerilog simulation...")
	if err := ivSim.RunTest(analysisDir, ivOutputPaths); err != nil {
		return nil, nil, fmt.Errorf("failed to run IVerilog: %v", err)
	}

	debug.Log("Running Verilator simulation...")
	if err := vlSim.RunTest(analysisDir, vlOutputPaths); err != nil {
		return nil, nil, fmt.Errorf("failed to run Verilator: %v", err)
	}

	return ivOutputPaths, vlOutputPaths, nil
}

// compareSimulationResults compares the current simulation outputs with the original ones from the mismatch directory.
func compareSimulationResults(
	mismatchPath string,
	ivOutputPaths, vlOutputPaths map[string]string,
	debug *utils.DebugLogger,
) error {
	debug.Log("\n=== Original vs. Current Simulation Results ===")

	// Find original output files
	origIvFiles, _ := filepath.Glob(filepath.Join(mismatchPath, "iv_*.hex"))
	origVlFiles, _ := filepath.Glob(filepath.Join(mismatchPath, "vl_*.hex"))

	// Create a set of all unique port names from both original and current simulator outputs
	portNames := make(map[string]bool)
	for portName := range ivOutputPaths {
		portNames[portName] = true
	}
	for portName := range vlOutputPaths {
		portNames[portName] = true
	}
	for _, ivPath := range origIvFiles {
		portName := strings.TrimPrefix(filepath.Base(ivPath), "iv_")
		portName = strings.TrimSuffix(portName, ".hex")
		portNames[portName] = true
	}
	for _, vlPath := range origVlFiles {
		portName := strings.TrimPrefix(filepath.Base(vlPath), "vl_")
		portName = strings.TrimSuffix(portName, ".hex")
		portNames[portName] = true
	}

	// Compare results for each port
	for portName := range portNames {
		// Original results paths
		origIvPath := filepath.Join(mismatchPath, fmt.Sprintf("iv_%s.hex", portName))
		origVlPath := filepath.Join(mismatchPath, fmt.Sprintf("vl_%s.hex", portName))

		// Current results paths (might not exist if port wasn't in the module anymore)
		newIvPath := ivOutputPaths[portName] // Will be empty if portName not in map
		newVlPath := vlOutputPaths[portName] // Will be empty if portName not in map

		// Read contents
		origIvContent, origIvErr := os.ReadFile(origIvPath)
		origVlContent, origVlErr := os.ReadFile(origVlPath)
		newIvContent, newIvErr := os.ReadFile(newIvPath) // Error if path is empty or file missing
		newVlContent, newVlErr := os.ReadFile(newVlPath) // Error if path is empty or file missing

		// Format values for display
		origIvValue := "<missing>"
		if origIvErr == nil {
			origIvValue = strings.TrimSpace(string(origIvContent))
		}
		origVlValue := "<missing>"
		if origVlErr == nil {
			origVlValue = strings.TrimSpace(string(origVlContent))
		}
		newIvValue := "<missing>"
		if newIvErr == nil {
			newIvValue = strings.TrimSpace(string(newIvContent))
		}
		newVlValue := "<missing>"
		if newVlErr == nil {
			newVlValue = strings.TrimSpace(string(newVlContent))
		}

		// Display comparison
		debug.Log("Port %s:", portName)
		debug.Log("  Original: IVerilog=%s, Verilator=%s", origIvValue, origVlValue)
		debug.Log("  Current:  IVerilog=%s, Verilator=%s", newIvValue, newVlValue)

		// Compare original and current outputs
		if origIvValue != newIvValue {
			debug.Log("  *** IVerilog OUTPUT CHANGED! ***")
		}
		if origVlValue != newVlValue {
			debug.Log("  *** Verilator OUTPUT CHANGED! ***")
		}

		// Compare outputs between simulators (current run)
		if newIvValue != newVlValue && newIvErr == nil &&
			newVlErr == nil { // Only compare if both current values exist
			debug.Log("  *** MISMATCH BETWEEN SIMULATORS STILL EXISTS ***")
		} else if origIvValue != origVlValue && origIvErr == nil && origVlErr == nil { // Check if original had mismatch
			if newIvValue == newVlValue && newIvErr == nil && newVlErr == nil { // And current doesn't
				debug.Log("  *** MISMATCH RESOLVED IN CURRENT RUN ***")
			}
		}
		debug.Log("")
	}
	return nil
}

// analyzeMismatchDirectory performs the analysis for a given mismatch directory.
func analyzeMismatchDirectory(
	mismatchPath, moduleName string,
	mocked, verbose bool,
	debug *utils.DebugLogger,
) error {
	analysisDir, err := setupAnalysisEnvironment()
	if err != nil {
		return fmt.Errorf("failed to set up analysis environment: %v", err)
	}
	debug.Log("Analysis environment set up in: %s", analysisDir)

	module, _, err := findAndPrepareVerilog(analysisDir, moduleName, mocked, debug)
	if err != nil {
		return fmt.Errorf("failed to prepare Verilog file: %v", err)
	}

	if err := generateDebugTestbench(module, analysisDir, debug); err != nil {
		return fmt.Errorf("failed to generate debug testbenches: %v", err)
	}

	if err := prepareInputFiles(mismatchPath, analysisDir, debug); err != nil {
		return fmt.Errorf("failed to prepare input files: %v", err)
	}

	ivSim, vlSim, err := setupAndCompileSimulators(analysisDir, module.Name, verbose, debug)
	if err != nil {
		return fmt.Errorf("failed to set up simulators: %v", err)
	}

	ivOutputPaths, vlOutputPaths, err := runSimulations(ivSim, vlSim, module, analysisDir, debug)
	if err != nil {
		return fmt.Errorf("failed to run simulations: %v", err)
	}

	if err := compareSimulationResults(mismatchPath, ivOutputPaths, vlOutputPaths, debug); err != nil {
		// Log comparison error but don't necessarily fail the whole analysis
		log.Printf("Warning: Error during result comparison: %v", err)
	}

	debug.Log("\nAnalysis complete. Debug files are in %s", analysisDir)
	return nil
}

func main() {
	verbose := flag.Bool("v", false, "Verbose output")
	moduleName := flag.String("module", "", "Module name (if different from filename)")
	mocked := flag.Bool("mocked", false, "Use mocked Verilog file")
	flag.Parse()

	// Initialize the debug logger
	debug = utils.NewDebugLogger(*verbose)

	// Check if we have a mismatch file or directory to analyze
	args := flag.Args()
	if len(args) < 1 {
		fmt.Println("Usage: analyze [-v] [-mocked] [-module <name>] <mismatch_file_or_dir>")
		os.Exit(1)
	}

	mismatchPath := args[0]
	// Allow specifying directory directly without needing .txt
	// mismatchPath = strings.TrimSuffix(mismatchPath, ".txt") // Keep this if .txt suffix is common

	// Check if path exists and is a directory
	fileInfo, err := os.Stat(mismatchPath)
	if err != nil {
		log.Fatalf("Failed to access mismatch path '%s': %v", mismatchPath, err)
	}

	if fileInfo.IsDir() {
		debug.Log("Analyzing mismatch directory: %s", mismatchPath)
		if err := analyzeMismatchDirectory(mismatchPath, *moduleName, *mocked, *verbose, debug); err != nil {
			log.Fatalf("Analysis failed: %v", err)
		}
	} else {
		debug.Log("Analyzing mismatch file: %s", mismatchPath)
		// If we're analyzing a mismatch file (not a directory)
		log.Println("Text-based mismatch file analysis not yet implemented.")
		log.Println("Please provide the path to a mismatch *directory* instead (e.g., mismatches/mismatch_23).")
		os.Exit(1) // Exit as this mode is not supported
	}
}
