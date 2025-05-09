package main

import (
	"flag"
	"os"
	"runtime"
	"time"

	"github.com/toby-bro/pfuzz/internal/fuzz"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

func main() {
	// Parse command-line flags
	numTests := flag.Int("n", 1000, "Number of test cases to run")
	strategy := flag.String("strategy", "simple", "Fuzzing strategy: simple, random, smart")
	workers := flag.Int("workers", runtime.NumCPU(), "Number of parallel workers")
	seedFlag := flag.Int64("seed", time.Now().UnixNano(), "Random seed")
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
	verilogFile := flag.String("file", "", "Path to Verilog file to fuzz (required)")
	moduleFlag := flag.String("module", "", "Module name to fuzz (if different from filename)")
	mutate := flag.Bool("mutate", false, "Mutate enums and structs in the testbench")
	maxAttempts := flag.Int("max-attempts", -1, "Maximum attempts to create a valid file")
	if *maxAttempts < 1 {
		switch *mutate {
		case true:
			*maxAttempts = 5
		case false:
			*maxAttempts = 1
		}
	}
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
	logger := utils.NewDebugLogger(verboseLevel)

	// Check if Verilog file is provided
	if *verilogFile == "" {
		logger.Fatal("Error: No Verilog file specified. Use -file option.")
	}

	// Create and setup fuzzer using the new package structure
	fuzzer := fuzz.NewFuzzer(
		*strategy,
		*workers,
		verboseLevel,
		*seedFlag,
		*verilogFile,
		*moduleFlag,
		*mutate,
		*maxAttempts,
	)

	if err := fuzzer.Setup(); err != nil {
		logger.Fatal("Setup failed: ", err)
	}

	// Run fuzzing
	if err := fuzzer.Run(*numTests); err != nil {
		os.Exit(1)
	}
}
