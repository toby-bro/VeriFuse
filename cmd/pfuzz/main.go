package main

import (
	"flag"
	"fmt"
	"os"
	"runtime"

	"github.com/toby-bro/pfuzz/internal/fuzz"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

type Config struct {
	// Common flags
	verilogFile  string
	workers      int
	verboseLevel int
	keepFiles    bool

	// Operation-specific flags
	numTests    int
	strategy    string
	maxAttempts int
	operation   fuzz.Operation
}

func parseVerboseFlags(fs *flag.FlagSet) int {
	vFlag := fs.Bool("v", false,
		"Verbose output (level 1). Higher levels (-vv, -vvv) take precedence.")
	vvFlag := fs.Bool("vv", false,
		"Verbose output (level 2). Higher level (-vvv) takes precedence.")
	vvvFlag := fs.Bool("vvv", false, "Verbose output (level 3).")

	if err := fs.Parse(os.Args[2:]); err != nil {
		fmt.Fprintf(os.Stderr, "Error parsing flags: %v\n", err)
		os.Exit(1)
	}

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

func addCommonFlags(fs *flag.FlagSet, config *Config) {
	fs.StringVar(&config.verilogFile, "file", "", "Path to Verilog file (required)")
	fs.IntVar(&config.workers, "workers", runtime.NumCPU(),
		"Number of parallel workers")
	fs.BoolVar(&config.keepFiles, "keep-files", false,
		"Keep generated files after operation (default: false)")
	fs.StringVar(&config.strategy, "strategy", "smart",
		"Fuzzing strategy: random, smart")
}

func setupFuzzCommand() (*Config, error) {
	config := &Config{operation: fuzz.OpFuzz}
	fs := flag.NewFlagSet("fuzz", flag.ExitOnError)
	fs.Usage = func() {
		fmt.Fprintf(os.Stderr, "Usage: %s fuzz [options]\n", os.Args[0])
		fmt.Fprintf(os.Stderr, "Perform fuzzing on Verilog files\n\n")
		fs.PrintDefaults()
	}

	addCommonFlags(fs, config)
	fs.IntVar(&config.numTests, "n", 1000, "Number of test cases to run")
	fs.IntVar(&config.maxAttempts, "max-attempts", 1,
		"Maximum attempts to create a valid file")

	config.verboseLevel = parseVerboseFlags(fs)

	return config, nil
}

func setupMutateCommand() (*Config, error) {
	config := &Config{operation: fuzz.OpMutate}
	fs := flag.NewFlagSet("mutate", flag.ExitOnError)
	fs.Usage = func() {
		fmt.Fprintf(os.Stderr, "Usage: %s mutate [options]\n", os.Args[0])
		fmt.Fprintf(os.Stderr, "Mutate enums and structs in the testbench\n\n")
		fs.PrintDefaults()
	}

	addCommonFlags(fs, config)
	fs.IntVar(&config.numTests, "n", 1000, "Number of test cases to run")
	fs.IntVar(&config.maxAttempts, "max-attempts", 5,
		"Maximum attempts to create a valid file")

	config.verboseLevel = parseVerboseFlags(fs)

	return config, nil
}

func setupCheckFileCommand() (*Config, error) {
	config := &Config{operation: fuzz.OpCheckFile}
	fs := flag.NewFlagSet("check-file", flag.ExitOnError)
	fs.Usage = func() {
		fmt.Fprintf(os.Stderr, "Usage: %s check-file [options]\n", os.Args[0])
		fmt.Fprintf(os.Stderr, "Check that all modules in the file are valid\n\n")
		fs.PrintDefaults()
	}

	addCommonFlags(fs, config)
	config.maxAttempts = 1
	config.numTests = config.workers

	config.verboseLevel = parseVerboseFlags(fs)

	return config, nil
}

func setupScoreSnippetsCommand() (*Config, error) {
	config := &Config{operation: fuzz.OpScoreSnippets}
	fs := flag.NewFlagSet("score-snippets", flag.ExitOnError)
	fs.Usage = func() {
		fmt.Fprintf(os.Stderr, "Usage: %s score-snippets [options]\n", os.Args[0])
		fmt.Fprintf(
			os.Stderr,
			"Evaluate snippets against simulators and synthesizers to generate scores\n\n",
		)
		fs.PrintDefaults()
	}

	addCommonFlags(fs, config)
	config.maxAttempts = 1
	config.numTests = 1

	config.verboseLevel = parseVerboseFlags(fs)

	return config, nil
}

func setupRewriteAsSnippetsCommand() (*Config, error) {
	config := &Config{operation: fuzz.OpRewriteValid}
	fs := flag.NewFlagSet("rewrite-as-snippets", flag.ExitOnError)
	fs.Usage = func() {
		fmt.Fprintf(os.Stderr, "Usage: %s rewrite-as-snippets [options]\n", os.Args[0])
		fmt.Fprintf(os.Stderr,
			"Rewrite the checked file to snippets if validated\n\n")
		fs.PrintDefaults()
	}

	addCommonFlags(fs, config)
	config.maxAttempts = 1
	config.numTests = config.workers

	config.verboseLevel = parseVerboseFlags(fs)
	config.verilogFile = "scoringFakeFile.sv"

	return config, nil
}

func printUsage() {
	fmt.Fprintf(os.Stderr, "Usage: %s <command> [options]\n\n", os.Args[0])
	fmt.Fprintf(os.Stderr, "Commands:\n")
	fmt.Fprintf(os.Stderr, "  fuzz                 Perform fuzzing on Verilog files\n")
	fmt.Fprintf(os.Stderr, "  mutate               Mutate enums and structs in the testbench\n")
	fmt.Fprintf(os.Stderr, "  check-file           Check that all modules in the file are valid\n")
	fmt.Fprintf(
		os.Stderr,
		"  score-snippets       Evaluate snippets against simulators and synthesizers\n",
	)
	fmt.Fprintf(os.Stderr,
		"  rewrite-as-snippets  Rewrite the checked file to snippets if validated\n\n")
	fmt.Fprintf(os.Stderr,
		"Use '%s <command> -h' for more information about a command.\n", os.Args[0])
}

func main() {
	if len(os.Args) < 2 {
		printUsage()
		os.Exit(1)
	}

	var config *Config
	var err error

	switch os.Args[1] {
	case "fuzz":
		config, err = setupFuzzCommand()
	case "mutate":
		config, err = setupMutateCommand()
	case "check-file":
		config, err = setupCheckFileCommand()
	case "score-snippets":
		config, err = setupScoreSnippetsCommand()
	case "rewrite-as-snippets":
		config, err = setupRewriteAsSnippetsCommand()
	case "-h", "--help", "help":
		printUsage()
		return
	default:
		fmt.Fprintf(os.Stderr, "Unknown command: %s\n\n", os.Args[1])
		printUsage()
		os.Exit(1)
	}

	if err != nil {
		fmt.Fprintf(os.Stderr, "Error setting up command: %v\n", err)
		os.Exit(1)
	}

	logger := utils.NewDebugLogger(config.verboseLevel)

	// Check if Verilog file is provided (not required for score-snippets)
	if config.verilogFile == "" && config.operation != fuzz.OpScoreSnippets {
		logger.Fatal("Error: No Verilog file specified. Use -file option.")
	}

	// Create and setup scheduler using the new package structure
	scheduler := fuzz.NewScheduler(
		config.strategy,
		config.workers,
		config.verboseLevel,
		config.verilogFile,
		config.operation,
		config.maxAttempts,
		config.keepFiles,
	)

	// For score-snippets operation, we don't need to setup simulators through the scheduler
	if config.operation == fuzz.OpScoreSnippets {
		// Just run the scoring operation directly
		if err := scheduler.RunScoreSnippets(); err != nil {
			os.Exit(1)
		}
		return
	}

	availableSimulators, availableSynthesizers, err := scheduler.Setup()
	if err != nil {
		logger.Fatal("Setup failed: ", err)
	}

	// Run operation
	if err := scheduler.Run(config.numTests, availableSimulators, availableSynthesizers); err != nil {
		os.Exit(1)
	}
}
