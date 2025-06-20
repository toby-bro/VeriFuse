package simulator

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"

	"github.com/toby-bro/pfuzz/pkg/utils"
)

var (
	sv2vUnexpectedString = `\bParse error: unexpected token '(\w+)'\b`
	Sv2vUnexpectedRegex  = regexp.MustCompile(sv2vUnexpectedString)
)

// TestSV2VTool checks if sv2v is available.
func TestSV2VTool() error {
	cmd := exec.Command("sv2v", "--version")
	var stderr bytes.Buffer
	var stdout bytes.Buffer
	cmd.Stderr = &stderr
	cmd.Stdout = &stdout

	if err := cmd.Run(); err != nil {
		return fmt.Errorf("sv2v check failed: %v - %s", err, stderr.String())
	}

	// Success - should have version output in stdout
	return nil
}

// TransformSV2V uses sv2v to transform SystemVerilog to plain Verilog
// srcPath: path to source SystemVerilog file
// destDir: destination directory for the output Verilog file
// Returns the path to the output Verilog file and any error
func TransformSV2V(
	moduleName string, srcPath string,
) error {
	// Check if source file exists and is readable
	srcInfo, err := os.Stat(srcPath)
	if err != nil {
		if os.IsNotExist(err) {
			return fmt.Errorf("source file does not exist: %s", srcPath)
		}
		return fmt.Errorf("error accessing source file %s: %v", srcPath, err)
	}

	// Check file size and fail early for empty files
	if srcInfo.Size() == 0 {
		return fmt.Errorf("source file is empty: %s", srcPath)
	}

	// Set the output path
	newFileName := filepath.Base(srcPath)
	// Replace .sv extension with .v if present
	if strings.HasSuffix(newFileName, ".sv") {
		newFileName = strings.TrimSuffix(newFileName, ".sv") + ".v"
	}
	outPath := filepath.Join(filepath.Dir(srcPath), newFileName)

	// Run sv2v with context for timeout
	cmd := exec.Command(
		"sv2v",
		"--top",
		moduleName,
		"-w", outPath, // Write to output file
		srcPath, // Input file
	)
	var stderr bytes.Buffer
	var stdout bytes.Buffer
	cmd.Stderr = &stderr
	cmd.Stdout = &stdout

	if err := cmd.Run(); err != nil {
		// Include both stdout and stderr in the error for better debugging
		return fmt.Errorf("sv2v conversion failed: %v\nstdout: %s\nstderr: %s",
			err, stdout.String(), stderr.String())
	}

	if err := utils.EnsureFileWritten(outPath, nil, 0); err != nil {
		return fmt.Errorf("failed to write output file %s: %v", outPath, err)
	}
	return nil
}
