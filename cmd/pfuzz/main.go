package main

import (
	"flag"
	"log"
	"os"
	"runtime"
	"time"

	"github.com/toby-bro/pfuzz/internal/fuzz"
)

func main() {
	// Parse command-line flags
	numTests := flag.Int("n", 1000, "Number of test cases to run")
	strategy := flag.String("strategy", "simple", "Fuzzing strategy: simple, random, smart")
	workers := flag.Int("workers", runtime.NumCPU(), "Number of parallel workers")
	seedFlag := flag.Int64("seed", time.Now().UnixNano(), "Random seed")
	verbose := flag.Bool("v", false, "Verbose output")
	verilogFile := flag.String("file", "", "Path to Verilog file to fuzz (required)")
	moduleFlag := flag.String("module", "", "Module name to fuzz (if different from filename)")
	flag.Parse()

	// Check if Verilog file is provided
	if *verilogFile == "" {
		log.Fatal("Error: No Verilog file specified. Use -file option.")
	}

	// Create and setup fuzzer using the new package structure
	fuzzer := fuzz.NewFuzzer(*strategy, *workers, *verbose, *seedFlag, *verilogFile, *moduleFlag)

	if err := fuzzer.Setup(); err != nil {
		log.Fatal("Setup failed: ", err)
	}

	// Run fuzzing
	if err := fuzzer.Run(*numTests); err != nil {
		os.Exit(1)
	}
}
