package synth

import (
	"bytes"
	"fmt"
	"os/exec"
	"strings"

	"github.com/toby-bro/pfuzz/pkg/utils"
)

func TestYosysTool() error {
	cmdYosys := exec.Command("yosys", "-V") // -V prints version and exits 0
	var stderrYosys bytes.Buffer
	cmdYosys.Stderr = &stderrYosys
	cmdYosys.Stdout = &stderrYosys // Some versions print to stdout
	if err := cmdYosys.Run(); err != nil {
		// Try `yosys -h` as a fallback for older versions or different behavior
		cmdYosysHelp := exec.Command("yosys", "-h")
		var stderrYosysHelp bytes.Buffer
		cmdYosysHelp.Stderr = &stderrYosysHelp
		cmdYosysHelp.Stdout = &stderrYosysHelp
		if errHelp := cmdYosysHelp.Run(); errHelp != nil ||
			!strings.Contains(stderrYosysHelp.String(), "Usage: yosys") {
			return fmt.Errorf(
				"yosys basic check failed. Ensure Yosys is installed and in PATH: %v - %s / %s",
				err,
				stderrYosys.String(),
				stderrYosysHelp.String(),
			)
		}
	}
	return nil
}

func TestSlangPlugin() error {
	cmdSlang := exec.Command("yosys", "-m", "slang", "-q", "-p", "help")
	var stderrSlang bytes.Buffer
	cmdSlang.Stderr = &stderrSlang
	cmdSlang.Stdout = &stderrSlang
	if err := cmdSlang.Run(); err != nil {
		return fmt.Errorf(
			"slang check failed. Ensure Slang is installed and available in Yosys: %v - %s",
			err,
			stderrSlang.String(),
		)
	}
	return nil
}

// YosysSynthOptions configures synthesis parameters
type YosysSynthOptions struct {
	UseSlang     bool
	Optimized    bool
	OutputFormat OutputFormat // "verilog" or "systemverilog"
}

type OutputFormat int

const (
	Verilog OutputFormat = iota
	SystemVerilog
)

// YosysSynth tries to read and synthesize the design it is given in input
// If first attempt fails, it will try with slang plugin (if available)
// Returns error only if all attempts fail
func YosysSynth(
	moduleName string,
	srcPath string,
	options *YosysSynthOptions,
) error {
	// Check if source file exists and is readable
	if !utils.FileExists(srcPath) {
		return fmt.Errorf("source file does not exist: %s", srcPath)
	}

	// Default options if not provided
	if options == nil {
		options = &YosysSynthOptions{
			UseSlang:     false,
			Optimized:    false,
			OutputFormat: SystemVerilog,
		}
	}

	outputPath := utils.AddSuffixToPath(srcPath, "-yosys")

	// Try synthesis with current settings first
	err := attemptYosysSynth(moduleName, srcPath, outputPath, options)
	if err == nil {
		return nil
	}

	// If not using slang and first attempt failed, try with slang
	if !options.UseSlang {
		slangOptions := *options
		slangOptions.UseSlang = true

		if slangErr := attemptYosysSynth(moduleName, srcPath, outputPath, &slangOptions); slangErr == nil {
			return nil
		}

		// Return original error if slang also fails
		return fmt.Errorf("yosys synthesis failed (tried both regular and slang): %v", err)
	}

	return err
}

// attemptYosysSynth performs a single synthesis attempt with given options
func attemptYosysSynth(
	moduleName string,
	srcPath string,
	outputPath string,
	options *YosysSynthOptions,
) error {
	// Build Yosys script
	var yosysScript string

	// Read input
	if options.UseSlang {
		yosysScript = fmt.Sprintf(
			"read_slang %s --top %s; prep -top %s",
			srcPath,
			moduleName,
			moduleName,
		)
	} else {
		yosysScript = fmt.Sprintf("read_verilog -sv %s; prep -top %s", srcPath, moduleName)
	}

	// Add optimization passes if requested
	if options.Optimized {
		yosysScript += "; proc; opt; fsm; opt; memory; opt; techmap; opt"
	} else {
		yosysScript += "; synth"
	}

	// Write output in requested format
	switch options.OutputFormat {
	case SystemVerilog:
		yosysScript += fmt.Sprintf("; write_verilog -sv -noattr %s", outputPath)
	case Verilog:
		fallthrough
	default: // "verilog"
		yosysScript += fmt.Sprintf("; write_verilog -noattr %s", outputPath)
	}

	// Execute Yosys command
	var cmd *exec.Cmd
	if options.UseSlang {
		cmd = exec.Command("yosys", "-m", "slang", "-p", yosysScript)
	} else {
		cmd = exec.Command("yosys", "-p", yosysScript)
	}

	var stderr bytes.Buffer
	cmd.Stderr = &stderr

	if err := cmd.Run(); err != nil {
		synthType := "regular"
		if options.UseSlang {
			synthType = "slang"
		}
		return fmt.Errorf("yosys %s synthesis failed: %v - %s", synthType, err, stderr.String())
	}

	return nil
}
