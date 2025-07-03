package main

import (
	"flag"
	"fmt"
	"os"
	"path/filepath"

	"github.com/toby-bro/pfuzz/pkg/testgen"
	"github.com/toby-bro/pfuzz/pkg/utils"
	"github.com/toby-bro/pfuzz/pkg/verilog"
)

func parseVerboseFlags(fs *flag.FlagSet) int {
	vFlag := fs.Bool(
		"v",
		false,
		"Verbose output (level 1). Higher levels (-vv, -vvv) take precedence.",
	)
	vvFlag := fs.Bool(
		"vv",
		false,
		"Verbose output (level 2). Higher level (-vvv) takes precedence.",
	)
	vvvFlag := fs.Bool("vvv", false, "Verbose output (level 3).")

	// Do not call fs.Parse here!

	switch {
	case *vvvFlag:
		return 4
	case *vvFlag:
		return 3
	case *vFlag:
		return 2
	default:
		return 1
	}
}

func main() {
	fs := flag.NewFlagSet("testbench", flag.ExitOnError)
	// Parse -d flag for output directory
	var outputDir string
	fs.StringVar(&outputDir, "d", "", "Output directory for generated testbenches (optional)")
	verboseLevel := parseVerboseFlags(fs)
	fs.Parse(os.Args[1:])

	args := fs.Args()
	if len(args) < 1 {
		fmt.Fprintf(os.Stderr, "Usage: %s [flags] <input.sv|input.v>\n", filepath.Base(os.Args[0]))
		os.Exit(1)
	}
	inputPath := args[0]

	content, err := utils.ReadFileContent(inputPath)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error reading file: %v\n", err)
		os.Exit(1)
	}

	vf, err := verilog.ParseVerilog(content, verboseLevel)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error parsing Verilog: %v\n", err)
		os.Exit(1)
	}
	if len(vf.Modules) == 0 {
		fmt.Fprintf(os.Stderr, "No modules found in file\n")
		os.Exit(1)
	}
	// Use the first module found
	var module *verilog.Module
	for _, m := range vf.Modules {
		module = m
		break
	}

	gen := testgen.NewGenerator(module, inputPath, vf)

	if outputDir != "" {
		// Use the provided output directory
		// Generate and write input files for all input ports (like generateAndPrepareInputs)
		inputs := make(map[string]string)
		for _, port := range module.Ports {
			if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
				inputs[port.Name] = "0" // You can replace this with your strategy if desired
			}
		}
		for portName, value := range inputs {
			inputPath := filepath.Join(outputDir, fmt.Sprintf("input_%s.hex", portName))
			if err := os.WriteFile(inputPath, []byte(value), 0o644); err != nil {
				fmt.Fprintf(os.Stderr, "Error writing input file %s: %v\n", inputPath, err)
				os.Exit(1)
			}
		}
		if err := gen.GenerateTestbenchesInDir(outputDir); err != nil {
			fmt.Fprintf(os.Stderr, "Error generating SystemVerilog testbench: %v\n", err)
			os.Exit(1)
		}
		if err := gen.GenerateCXXRTLTestbench(outputDir); err != nil {
			fmt.Fprintf(os.Stderr, "Error generating CXXRTL testbench: %v\n", err)
			os.Exit(1)
		}
		return
	}

	// Default: generate a testbench with hardcoded random inputs and print to stdout
	// Import the strategy here to avoid cycles
	randomStrategy := struct {
		GenerateTestCase func(int) map[string]string
	}{
		GenerateTestCase: func(_ int) map[string]string {
			// fallback: all zeros
			inputs := make(map[string]string)
			for _, port := range module.Ports {
				if port.Direction == verilog.INPUT || port.Direction == verilog.INOUT {
					inputs[port.Name] = "0"
				}
			}
			return inputs
		},
	}
	// Replace above with your real strategy if you want
	inputs := randomStrategy.GenerateTestCase(0)
	testbench := gen.GenerateSVTestbenchWithInputs(inputs)
	fmt.Print(testbench)
}
