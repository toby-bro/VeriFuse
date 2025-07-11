package synth

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"

	"github.com/toby-bro/pfuzz/pkg/utils"
)

// semaphore to limit concurrent Vivado synths to 5
var vivadoSemaphore = make(chan struct{}, 5)

func TestVivadoTool() error {
	cmd := exec.Command("vivado", "-version")
	var stderr bytes.Buffer
	var stdout bytes.Buffer
	cmd.Stderr = &stderr
	cmd.Stdout = &stdout

	vivadoSemaphore <- struct{}{}
	defer func() { <-vivadoSemaphore }()

	if err := cmd.Run(); err != nil {
		return fmt.Errorf("Vivado check failed: %v - %s", err, stderr.String())
	}

	// Success - should have version output in stdout
	return nil
}

var vivadoScriptTemplate = `
set_msg_config -id {Synth 8-5821} -new_severity {WARNING}

read_verilog %s
synth_design -top %s
write_verilog %s`

func vivadoSynth(
	moduleName string,
	srcPath string,
) error {
	srcInfo, err := os.Stat(srcPath)
	if err != nil {
		if os.IsNotExist(err) {
			return fmt.Errorf("source file does not exist: %s", srcPath)
		}
		return fmt.Errorf("error accessing source file %s: %v", srcPath, err)
	}

	if srcInfo.Size() == 0 {
		return fmt.Errorf("source file is empty: %s", srcPath)
	}

	outPath := utils.ChangeExtension(srcPath, "v")
	outPath = utils.AddSuffixToPath(outPath, VIVADO.String())

	// Write vivado script to a temporary file
	scriptContent := fmt.Sprintf(
		vivadoScriptTemplate,
		srcPath,
		moduleName,
		outPath,
	)
	scriptFile, err := os.CreateTemp("", "vivado_script_*.tcl")
	if err != nil {
		return fmt.Errorf("failed to create temporary script file: %v", err)
	}
	defer os.Remove(scriptFile.Name()) // Clean up temporary file

	if _, err := scriptFile.WriteString(scriptContent); err != nil {
		return fmt.Errorf("failed to write to temporary script file: %v", err)
	}

	cmd := exec.Command(
		"vivado",
		"-mode",
		"batch",
		"-source",
		scriptFile.Name(),
	)
	var stderr bytes.Buffer
	var stdout bytes.Buffer
	cmd.Stderr = &stderr
	cmd.Stdout = &stdout

	if err := cmd.Run(); err != nil {
		return fmt.Errorf("vivado synthesis failed: %v\nstdout: %s\nstderr: %s",
			err, stdout.String(), stderr.String())
	}

	if err := utils.EnsureFileWritten(outPath, nil, 0); err != nil {
		return fmt.Errorf("failed to write output file %s: %v", outPath, err)
	}
	return nil
}

func VivadoSynthSync(
	moduleName string,
	srcPath string,
) error {
	// Acquire a slot in the Vivado semaphore
	vivadoSemaphore <- struct{}{}
	defer func() { <-vivadoSemaphore }()

	if err := vivadoSynth(moduleName, srcPath); err != nil {
		return fmt.Errorf("Vivado synthesis failed: %v", err)
	}

	return nil
}
