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

func getMockedVerilogFile() string {
	tmpGen, err := os.ReadDir("tmp_gen")
	if err != nil {
		return ""
	}
	for _, file := range tmpGen {
		if strings.HasSuffix(file.Name(), "_mocked.sv") {
			return filepath.Join("tmp_gen", file.Name())
		}
	}
	return ""
}

func main() {
	verbose := flag.Bool("v", false, "Verbose output")
	moduleName := flag.String("module", "", "Module name (if different from filename)")
	flag.Parse()

	// Initialize the debug logger
	debug = utils.NewDebugLogger(*verbose)

	// Check if we have a mismatch file or directory to analyze
	args := flag.Args()
	if len(args) < 1 {
		fmt.Println("Usage: analyze [-v] <mismatch_file_or_dir> [--step]")
		os.Exit(1)
	}

	mismatchPath := args[0]

	mismatchPath = strings.TrimSuffix(mismatchPath, ".txt")

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

	// If path is a directory, use the stored simulation results
	if isMismatchDir {
		// Find the mocked Verilog file
		verilogFile := getMockedVerilogFile()
		if verilogFile == "" {
			log.Fatal("Error: No mocked Verilog file found in tmp_gen directory.")
		}

		// Determine module name from the file if not specified
		module, err := verilog.ParseVerilogFile(verilogFile, *moduleName)
		if err != nil {
			log.Fatalf("Failed to parse Verilog file: %v", err)
		}

		debug.Log("Using module: %s", module.Name)

		// Copy the mocked Verilog file to the analysis directory
		analysisMockedFile := filepath.Join(analysisDir, filepath.Base(verilogFile))
		if err := utils.CopyFile(verilogFile, analysisMockedFile); err != nil {
			log.Fatalf("Failed to copy mocked Verilog file: %v", err)
		}

		// Generate debug testbenches
		if err := generateDebugTestbench(module); err != nil {
			log.Fatalf("Failed to generate debug testbenches: %v", err)
		}

		// Copy all input files from the mismatch directory to the analysis directory
		inputFiles, _ := filepath.Glob(filepath.Join(mismatchPath, "input_*.hex"))
		if len(inputFiles) > 0 {
			debug.Log("Found %d input files:", len(inputFiles))
			for _, f := range inputFiles {
				content, _ := os.ReadFile(f)
				portName := strings.TrimPrefix(filepath.Base(f), "input_")
				portName = strings.TrimSuffix(portName, ".hex")
				debug.Log("  %s = %s", portName, strings.TrimSpace(string(content)))

				// Copy the input file to analysis directory
				destPath := filepath.Join(analysisDir, filepath.Base(f))
				if err := utils.CopyFile(f, destPath); err != nil {
					log.Fatalf("Failed to copy input file %s: %v", f, err)
				}
			}
		} else {
			log.Fatal("No input files found in mismatch directory")
		}

		// Create simulator instances
		ivSim := simulator.NewIVerilogSimulator(analysisDir, *verbose)
		vlSim := simulator.NewVerilatorSimulator(analysisDir, module.Name)

		// Compile the simulators
		debug.Log("Compiling IVerilog simulator...")
		if err := ivSim.Compile(); err != nil {
			log.Fatal("Failed to compile IVerilog:", err)
		}

		debug.Log("Compiling Verilator simulator...")
		if err := vlSim.Compile(); err != nil {
			log.Fatal("Failed to compile Verilator:", err)
		}

		// Create dynamic output paths based on module outputs
		ivOutputPaths := make(map[string]string)
		vlOutputPaths := make(map[string]string)

		for _, port := range module.Ports {
			if port.Direction == verilog.OUTPUT {
				ivOutputPaths[port.Name] = filepath.Join(analysisDir, fmt.Sprintf("iv_%s.hex", port.Name))
				vlOutputPaths[port.Name] = filepath.Join(analysisDir, fmt.Sprintf("vl_%s.hex", port.Name))
			}
		}

		// Run simulations
		debug.Log("Running IVerilog simulation...")
		if err := ivSim.RunTest(analysisDir, ivOutputPaths); err != nil {
			log.Fatal("Failed to run IVerilog:", err)
		}

		debug.Log("Running Verilator simulation...")
		if err := vlSim.RunTest(analysisDir, vlOutputPaths); err != nil {
			log.Fatal("Failed to run Verilator:", err)
		}

		// Compare simulation results with saved results
		debug.Log("\n=== Current Simulation Results ===")

		// Compare with originally saved outputs
		ivFiles, _ := filepath.Glob(filepath.Join(mismatchPath, "iv_*.hex"))
		vlFiles, _ := filepath.Glob(filepath.Join(mismatchPath, "vl_*.hex"))

		// Create a set of all unique port names from both simulator outputs
		portNames := make(map[string]bool)

		// Extract port names from ivFiles
		for _, ivPath := range ivFiles {
			portName := strings.TrimPrefix(filepath.Base(ivPath), "iv_")
			portName = strings.TrimSuffix(portName, ".hex")
			portNames[portName] = true
		}

		// Extract port names from vlFiles
		for _, vlPath := range vlFiles {
			portName := strings.TrimPrefix(filepath.Base(vlPath), "vl_")
			portName = strings.TrimSuffix(portName, ".hex")
			portNames[portName] = true
		}

		// Compare current results with saved results
		debug.Log("\n=== Original vs. Current Simulation Results ===")

		for portName := range portNames {
			// Original results
			origIvPath := filepath.Join(mismatchPath, fmt.Sprintf("iv_%s.hex", portName))
			origVlPath := filepath.Join(mismatchPath, fmt.Sprintf("vl_%s.hex", portName))

			// Current results
			newIvPath := ivOutputPaths[portName]
			newVlPath := vlOutputPaths[portName]

			var origIvContent, origVlContent, newIvContent, newVlContent []byte
			var origIvErr, origVlErr, newIvErr, newVlErr error

			// Read original outputs
			origIvContent, origIvErr = os.ReadFile(origIvPath)
			origVlContent, origVlErr = os.ReadFile(origVlPath)

			// Read current outputs
			if _, err := os.Stat(newIvPath); err == nil {
				newIvContent, newIvErr = os.ReadFile(newIvPath)
			}
			if _, err := os.Stat(newVlPath); err == nil {
				newVlContent, newVlErr = os.ReadFile(newVlPath)
			}

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

			// Compare outputs between simulators
			if newIvValue != newVlValue {
				debug.Log("  *** MISMATCH BETWEEN SIMULATORS STILL EXISTS ***")
			} else if origIvValue != origVlValue {
				debug.Log("  *** MISMATCH RESOLVED IN CURRENT RUN ***")
			}

			debug.Log("")
		}

		return
	}

	// If we're analyzing a mismatch file (not a directory)
	debug.Log("Text-based mismatch file analysis not yet implemented")
	debug.Log("Please use a mismatch directory instead, e.g., mismatches/mismatch_23")
}

// generateDebugTestbench creates a testbench with debug instrumentation
func generateDebugTestbench(module *verilog.Module) error {
	// Generate a specialized testbench for debugging
	gen := testgen.NewGenerator(module)

	// Generate both the SystemVerilog and C++ testbenches
	if err := gen.GenerateTestbenches(); err != nil {
		return fmt.Errorf("failed to generate debug testbenches: %v", err)
	}

	// Copy testbenches to analysis directory
	analysisDir := filepath.Join(utils.TMP_DIR, "analysis")

	svTestbench := filepath.Join(utils.TMP_DIR, "testbench.sv")
	cppTestbench := filepath.Join(utils.TMP_DIR, "testbench.cpp")

	if err := utils.CopyFile(svTestbench, filepath.Join(analysisDir, "testbench.sv")); err != nil {
		return fmt.Errorf("failed to copy SV testbench: %v", err)
	}

	if err := utils.CopyFile(cppTestbench, filepath.Join(analysisDir, "testbench.cpp")); err != nil {
		return fmt.Errorf("failed to copy C++ testbench: %v", err)
	}

	return nil
}
