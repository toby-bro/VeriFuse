package main

import (
	"flag"
	"fmt"
	"log"
	"os"
	"path/filepath"
	"strings"

	"github.com/toby-bro/pfuzz/internal/simulator"
	"github.com/toby-bro/pfuzz/internal/verilog"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

// Debug logger for both normal and debug messages
var debug *utils.DebugLogger

func main() {
	verbose := flag.Bool("v", false, "Verbose output")
	verilogFile := flag.String("file", "", "Path to Verilog file to analyze (required)")
	moduleName := flag.String("module", "", "Module name (if different from filename)")
	flag.Parse()

	// Initialize the debug logger
	debug = utils.NewDebugLogger(*verbose)

	// Check if file is provided
	if *verilogFile == "" {
		log.Fatal("Error: No Verilog file specified. Use -file option.")
	}

	// Determine module name from the file if not specified
	module, err := verilog.ParseVerilogFile(*verilogFile, *moduleName)
	if err != nil {
		log.Fatalf("Failed to parse Verilog file: %v", err)
	}

	debug.Log("Using module: %s", module.Name)

	// Check if we have a mismatch file to analyze
	args := flag.Args()
	if len(args) < 1 {
		fmt.Println("Usage: analyze [-v] -file <verilog_file> <mismatch_file_or_dir> [--step]")
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
		debug.Log("Using saved simulation results from mismatch directory")

		// Find all input files in the mismatch directory
		inputFiles, _ := filepath.Glob(filepath.Join(mismatchPath, "input_*.hex"))

		if len(inputFiles) > 0 {
			debug.Log("Found %d input files:", len(inputFiles))
			for _, f := range inputFiles {
				content, _ := os.ReadFile(f)
				portName := strings.TrimPrefix(filepath.Base(f), "input_")
				portName = strings.TrimSuffix(portName, ".hex")
				debug.Log("  %s = %s", portName, strings.TrimSpace(string(content)))
			}
		}

		// Find all output files
		ivFiles, _ := filepath.Glob(filepath.Join(mismatchPath, "iv_*.hex"))
		vlFiles, _ := filepath.Glob(filepath.Join(mismatchPath, "vl_*.hex"))

		debug.Log("\n=== Simulation Results (from saved files) ===")

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

		// Process all unique ports
		for portName := range portNames {
			ivPath := filepath.Join(mismatchPath, "iv_"+portName+".hex")
			vlPath := filepath.Join(mismatchPath, "vl_"+portName+".hex")

			// Check if both files exist
			ivExists := false
			vlExists := false
			var ivContent, vlContent []byte
			var ivErr, vlErr error

			// Read IVerilog output if it exists
			if ivContent, ivErr = os.ReadFile(ivPath); ivErr == nil {
				ivExists = true
			}

			// Read Verilator output if it exists
			if vlContent, vlErr = os.ReadFile(vlPath); vlErr == nil {
				vlExists = true
			}

			// Skip if neither output exists
			if !ivExists && !vlExists {
				continue
			}

			// Display outputs and compare if both exist
			if ivExists && vlExists {
				ivValue := strings.TrimSpace(string(ivContent))
				vlValue := strings.TrimSpace(string(vlContent))

				debug.Log("Port %s: IVerilog=%s, Verilator=%s", portName, ivValue, vlValue)

				if ivValue != vlValue {
					debug.Log("*** MISMATCH DETECTED IN PORT %s ***", portName)
				}
			} else if ivExists {
				debug.Log("Port %s: IVerilog=%s, Verilator=<missing>",
					portName, strings.TrimSpace(string(ivContent)))
			} else {
				debug.Log("Port %s: IVerilog=<missing>, Verilator=%s",
					portName, strings.TrimSpace(string(vlContent)))
			}
		}

		return
	}

	// Add debug instrumentation to the Verilog files if in step mode
	if stepMode {
		// In step mode, modify the testbench to output detailed signals
		generateDebugTestbench(module)
	}

	// Update simulator creation to use parsed module name
	ivSim := simulator.NewIVerilogSimulator(analysisDir, *verbose)
	vlSim := simulator.NewVerilatorSimulator(analysisDir, module.Name)

	debug.Log("Running IVerilog simulation...")
	if err := ivSim.Compile(); err != nil {
		log.Fatal("Failed to compile IVerilog:", err)
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

	// Run simulators with dynamic output paths
	if err := ivSim.RunTest(analysisDir, ivOutputPaths); err != nil {
		log.Fatal("Failed to run IVerilog:", err)
	}

	debug.Log("Running Verilator simulation...")
	if err := vlSim.Compile(); err != nil {
		log.Fatal("Failed to compile Verilator:", err)
	}

	if err := vlSim.RunTest(analysisDir, vlOutputPaths); err != nil {
		log.Fatal("Failed to run Verilator:", err)
	}

	// Compare all output ports generically
	debug.Log("\n=== Simulation Results ===")

	for portName, ivPath := range ivOutputPaths {
		vlPath := vlOutputPaths[portName]

		ivContent, err := os.ReadFile(ivPath)
		if err != nil {
			log.Fatalf("Failed to read IVerilog output for %s: %v", portName, err)
		}

		vlContent, err := os.ReadFile(vlPath)
		if err != nil {
			log.Fatalf("Failed to read Verilator output for %s: %v", portName, err)
		}

		ivValue := strings.TrimSpace(string(ivContent))
		vlValue := strings.TrimSpace(string(vlContent))

		debug.Log("Port %s: IVerilog=%s, Verilator=%s", portName, ivValue, vlValue)

		if ivValue != vlValue {
			debug.Log("*** MISMATCH DETECTED IN PORT %s ***", portName)
		}
	}
}

// generateDebugTestbench creates a testbench with debug instrumentation
func generateDebugTestbench(module *verilog.Module) {
	// Create a modified testbench that outputs intermediate values
	// For now, just a placeholder for future implementation
	return
}
