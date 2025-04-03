package main

import (
	"flag"
	"log"
	"os"
	"runtime"
	"time"

	"github.com/jns/pfuzz/internal/fuzz"
)

func main() {
	// Parse command-line flags
	numTests := flag.Int("n", 1000, "Number of test cases to run")
	strategy := flag.String("strategy", "opcode-aware", "Fuzzing strategy: simple, opcode-aware, mutation")
	workers := flag.Int("workers", runtime.NumCPU(), "Number of parallel workers")
	seedFlag := flag.Int64("seed", time.Now().UnixNano(), "Random seed")
	verbose := flag.Bool("v", false, "Verbose output")
	flag.Parse()

	// Create and setup fuzzer using the new package structure
	fuzzer := fuzz.NewFuzzer(*strategy, *workers, *verbose, *seedFlag)

	if err := fuzzer.Setup(); err != nil {
		// Configure logging based on verbose flag
		log.Fatal("Setup failed:", err)
	}

	// Run fuzzing
	if err := fuzzer.Run(*numTests); err != nil {
		os.Exit(1)
	}
}
