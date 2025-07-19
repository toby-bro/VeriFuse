package main

import (
	"flag"
	"fmt"
	"os"

	"github.com/toby-bro/pfuzz/pkg/mutate"
	"github.com/toby-bro/pfuzz/pkg/utils"
	"github.com/toby-bro/pfuzz/pkg/verilog"
)

func main() {
	fs := flag.NewFlagSet("generate", flag.ExitOnError)
	var file string
	fs.StringVar(&file, "file", "", "Path to a verilog file to generate from")
	var verbose bool
	fs.BoolVar(&verbose,
		"v",
		false,
		"Verbose output",
	)
	var outputFile string
	fs.StringVar(&outputFile, "o", "", "Path to the output verilog file (shorthand)")
	var g int
	fs.IntVar(&g, "g", 0, "The expected value of numbers of injected modules (default is random)")

	if err := fs.Parse(os.Args[1:]); err != nil {
		fmt.Fprintf(os.Stderr, "Error parsing flags: %v\n", err)
		os.Exit(1)
	}

	var verboseLevel int
	switch verbose {
	case true:
		verboseLevel = 4
	default:
		verboseLevel = 1
	}

	var svFile *verilog.VerilogFile
	if file != "" {
		content, err := utils.ReadFileContent(file)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error reading file: %v\n", err)
			os.Exit(1)
		}
		svFile, err = verilog.ParseVerilog(content, verboseLevel)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error parsing verilog: %v\n", err)
			os.Exit(1)
		}
	} else {
		svFile = verilog.NewVerilogFile("snippet.sv")
		module := svFile.CreateModule("snippet")
		module.Ports = []*verilog.Port{
			{Name: "clk", Direction: verilog.INPUT},
			{Name: "reset", Direction: verilog.INPUT},
		}
	}
	var ginv float32
	if g == 0 {
		ginv = 0
	} else {
		ginv = 1 / float32(g)
	}
	mutateSuccessful := mutate.MutateFile(svFile, ginv, "generate", verboseLevel)
	if !mutateSuccessful {
		fmt.Fprintln(os.Stderr, "Failed to mutate the Verilog file")
		os.Exit(2)
	}
	newContent, err := verilog.PrintVerilogFile(svFile)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error printing Verilog file: %v\n", err)
		os.Exit(1)
	}
	if outputFile != "" {
		if err := utils.WriteFileContent(outputFile, newContent); err != nil {
			fmt.Fprintf(os.Stderr, "Error writing output file: %v\n", err)
			os.Exit(1)
		}
	} else {
		fmt.Print(newContent)
	}
}
