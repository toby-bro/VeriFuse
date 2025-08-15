package synth

import (
	"bytes"
	"context"
	"fmt"
	"math/rand"
	"os/exec"
	"regexp"
	"strings"

	"github.com/toby-bro/pfuzz/pkg/utils"
)

var YOSYS_OPTIMISATIONS = []string{
	"opt_expr",
	"opt_expr -fine",
	"opt_expr -keepdc",
	"opt_merge -nomux",
	"opt",
	"opt_muxtree",
	"opt_merge",
	"opt_rmdff",
	"opt_clean",
	"opt_clean -purge",
	"opt_reduce",
	"opt_demorgan",
	"opt_mem",
	"opt_lut",
	"opt_dff -nodffe",
	"opt_dff",
	"fsm_detect",
	"fsm",
	"fsm_extract",
	"fsm_opt",
	"fsm_expand",
	"fsm_recode",
	"fsm_map",
	"fsm -norecodec",
	"abc",
	"hierarchy",
	"techmap",
	"proc",
}

func TestYosysTool() error {
	cmdYosys := exec.Command("yosys", "-V") //nolint: noctx
	var stderrYosys bytes.Buffer
	cmdYosys.Stderr = &stderrYosys
	cmdYosys.Stdout = &stderrYosys // Some versions print to stdout
	if err := cmdYosys.Run(); err != nil {
		// Try `yosys -h` as a fallback for older versions or different behavior
		cmdYosysHelp := exec.Command("yosys", "-h") //nolint: noctx
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
	cmdSlang := exec.Command("yosys", "-m", "slang", "-q", "-p", "help") //nolint: noctx
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
	ctx context.Context,
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

	outputPath := utils.AddSuffixToPath(srcPath, YOSYS.String())

	// Try synthesis with current settings first
	err := attemptYosysSynth(ctx, moduleName, srcPath, outputPath, options)
	if err == nil {
		return nil
	}

	// If not using slang and first attempt failed, try with slang
	if !options.UseSlang {
		slangOptions := *options
		slangOptions.UseSlang = true

		if slangErr := attemptYosysSynth(ctx, moduleName, srcPath, outputPath, &slangOptions); slangErr == nil {
			return nil
		}

		// Return original error if slang also fails
		return fmt.Errorf("yosys synthesis failed (tried both regular and slang): %v", err)
	}

	return err
}

var (
	YosysUnsupportedPattern = `ERROR: (syntax error, unexpected TOK_PROPERTY|Can't resolve (function|task) name .\\?\$(monitoroff|info|sampled|asserton|assertoff|monitoroff|monitoron)')`
	YosysUnsupportedRegex   = regexp.MustCompile(YosysUnsupportedPattern)
)

func YosysFailedCuzUnsupportedFeature(log error) (bool, error) {
	if log == nil {
		return false, nil
	}
	// Check if the error matches unsupported feature patterns
	if match := YosysUnsupportedRegex.FindStringSubmatch(log.Error()); len(match) > 0 {
		return true, fmt.Errorf("yosys unsupported feature: %s", match[0])
	}
	return false, nil
}

// attemptYosysSynth performs a single synthesis attempt with given options
func attemptYosysSynth(
	ctx context.Context,
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
	switch rand.Intn(5) {
	case 0:
		yosysScript += "; proc; opt; fsm; opt; memory; opt; techmap; opt"
	case 1:
		yosysScript += "; synth"
	case 2, 3, 4:
		// select a random number of optimisations and apply them in a random order from the YOSYS_OPTIMISATON slice
		numOptimizations := rand.Intn(len(YOSYS_OPTIMISATIONS)) + 1
		rand.Shuffle(len(YOSYS_OPTIMISATIONS), func(i, j int) {
			YOSYS_OPTIMISATIONS[i], YOSYS_OPTIMISATIONS[j] = YOSYS_OPTIMISATIONS[j], YOSYS_OPTIMISATIONS[i]
		})
		yosysScript += "; " + strings.Join(YOSYS_OPTIMISATIONS[:numOptimizations], "; ")
	}

	// Write output in requested format
	switch options.OutputFormat {
	case SystemVerilog:
		yosysScript += "; write_verilog -sv -noattr " + outputPath
	case Verilog:
		fallthrough
	default: // "verilog"
		yosysScript += "; write_verilog -noattr " + outputPath
	}

	// Execute Yosys command
	var cmd *exec.Cmd
	if options.UseSlang {
		cmd = exec.CommandContext(ctx, "yosys", "-m", "slang", "-p", yosysScript)
	} else {
		cmd = exec.CommandContext(ctx, "yosys", "-p", yosysScript)
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
	// add a comment with the Yosys script used at the top of the generated file at outputPath
	comment := fmt.Sprintf("// Yosys script used:\n%s\n", yosysScript)
	if err := utils.PrependToFile(outputPath, comment); err != nil {
		return fmt.Errorf("failed to add comment to output file: %v", err)
	}

	return nil
}
