package main

import (
	"flag"
	"os"
	"runtime"

	"github.com/toby-bro/pfuzz/internal/fuzz"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

func main() {
	// Parse command-line flags
	numTests := flag.Int("n", 1000, "Number of test cases to run")
	strategy := flag.String("strategy", "smart", "Fuzzing strategy: random, smart")
	workers := flag.Int("workers", runtime.NumCPU(), "Number of parallel workers")
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
	mutate := flag.Bool("mutate", false, "Mutate enums and structs in the testbench")
	maxAttempts := flag.Int("max-attempts", -1, "Maximum attempts to create a valid file")
	checkFile := flag.Bool(
		"check-file", false, "Check that all the modules in the file are valid",
	)
	rewriteAsSnippets := flag.Bool(
		"rewrite-as-snippets",
		false,
		"Rewrite the checked file to snippets if validated",
	)
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

	var operation fuzz.Operation
	if *mutate {
		operation = fuzz.OpFuzz
	}

	// Check if Verilog file is provided
	if *verilogFile == "" {
		logger.Fatal("Error: No Verilog file specified. Use -file option.")
	}

	if *checkFile {
		logger.Info("Checking Verilog file for valid modules...")
		*maxAttempts = 1
		switch *rewriteAsSnippets {
		case true:
			operation = fuzz.OpRewriteValid
		case false:
			operation = fuzz.OpCheckFile
		}
		if *numTests == 1000 {
			*numTests = *workers
		}
	}

	// Create and setup scheduler using the new package structure
	scheduler := fuzz.NewScheduler(
		*strategy,
		*workers,
		verboseLevel,
		*verilogFile,
		operation,
		*maxAttempts,
	)

	if err := scheduler.Setup(); err != nil {
		logger.Fatal("Setup failed: ", err)
	}

	// Run fuzzing
	if err := scheduler.Run(*numTests); err != nil {
		os.Exit(1)
	}
}
