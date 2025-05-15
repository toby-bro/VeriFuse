package fuzz

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"

	"github.com/toby-bro/pfuzz/internal/verilog"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

func compareOutputValues(ivValue, vlValue string) bool {
	ivNorm := strings.TrimSpace(strings.ToLower(ivValue))
	vlNorm := strings.TrimSpace(strings.ToLower(vlValue))
	if ivNorm == vlNorm {
		return true
	}
	if (ivNorm == "00" && vlNorm == "xx") || (ivNorm == "xx" && vlNorm == "00") {
		return true
	}
	if (ivNorm == "0" && vlNorm == "x") || (ivNorm == "x" && vlNorm == "0") {
		return true
	}
	if len(ivNorm) == len(vlNorm) && ivNorm != vlNorm {
		if strings.Contains(ivNorm, "x") || strings.Contains(vlNorm, "x") {
			equivalent := true
			for i := 0; i < len(ivNorm); i++ {
				charMatch := ivNorm[i] == vlNorm[i] ||
					(ivNorm[i] == 'x' && vlNorm[i] == '0') ||
					(ivNorm[i] == '0' && vlNorm[i] == 'x')
				if !charMatch {
					equivalent = false
					break
				}
			}
			return equivalent
		}
	}
	return false
}

func (f *Fuzzer) compareSimulationResults(
	ivResult, vlResult map[string]string,
) (bool, map[string]string) {
	mismatch := false
	mismatchDetails := make(map[string]string)
	for portName, ivValue := range ivResult {
		if vlValue, exists := vlResult[portName]; exists {
			if !compareOutputValues(ivValue, vlValue) {
				mismatch = true
				mismatchDetails[portName] = fmt.Sprintf(
					"IVerilog=%s, Verilator=%s",
					ivValue,
					vlValue,
				)
			}
		} else {
			mismatch = true
			mismatchDetails[portName] = fmt.Sprintf("IVerilog=%s, Verilator=MISSING", ivValue)
			f.debug.Debug("Warning: Output for port %s missing from Verilator result", portName)
		}
	}
	for portName, vlValue := range vlResult {
		if _, exists := ivResult[portName]; !exists {
			mismatch = true
			mismatchDetails[portName] = "IVerilog=MISSING, Verilator=" + vlValue
			f.debug.Debug("Warning: Output for port %s missing from IVerilog result", portName)
		}
	}
	return mismatch, mismatchDetails
}

func (f *Fuzzer) handleMismatch(
	testIndex int,
	testDir string,
	testCase map[string]string,
	mismatchDetails map[string]string,
	workerModule *verilog.Module,
) {
	f.debug.Info(
		"[%s] Mismatch found in test %d: for module %s",
		testDir,
		testIndex,
		workerModule.Name,
	)
	f.debug.Info("Inputs:")
	for portName, value := range testCase {
		f.debug.Info("  %s = %s", portName, value)
	}
	f.debug.Info("Mismatched outputs:")
	for portName, detail := range mismatchDetails {
		f.debug.Info("  %s: %s", portName, detail)
	}
	mismatchDir := filepath.Join(utils.MISMATCHES_DIR, fmt.Sprintf("mismatch_%d", testIndex))
	if err := os.MkdirAll(mismatchDir, 0o755); err != nil {
		f.debug.Error("Failed to create mismatch directory %s: %v", mismatchDir, err)
	} else {
		// Copy all the files from the test directory to the mismatch directory
		f.debug.Debug("Copying test files to mismatch directory %s", mismatchDir)
		if err := utils.CopyDir(testDir, mismatchDir); err != nil {
			f.debug.Error("Failed to copy test files to mismatch directory %s: %v", mismatchDir, err)
		}
		summaryPath := filepath.Join(mismatchDir, fmt.Sprintf("mismatch_%d_summary.txt", testIndex))
		fileContent := fmt.Sprintf(
			"Test case %d\n\nInputs:\n", testIndex)
		for portName, value := range testCase {
			fileContent += fmt.Sprintf("  %s = %s\n", portName, value)
		}
		fileContent += "\nMismatched outputs:\n"
		for portName, detail := range mismatchDetails {
			fileContent += fmt.Sprintf("  %s: %s\n", portName, detail)
		}
		f.debug.Debug("Writing mismatch summary to %s", summaryPath)
		err := utils.WriteFileContent(summaryPath, fileContent)
		if err != nil {
			f.debug.Error("Failed to write mismatch summary to %s: %v", summaryPath, err)
		}
		// also copy the file that was tested and the testbench
		testFilePath := filepath.Join(testDir, "../")
		testFilePath = filepath.Join(testFilePath, f.svFile.Name)
		if err := utils.CopyFile(testFilePath, mismatchDir+"/"+f.svFile.Name); err != nil {
			f.debug.Error("Failed to copy test file %s to mismatch directory %s: %v", testFilePath, mismatchDir, err)
		}
		testbenchPath := filepath.Join(testDir, "../testbench.sv")
		if err := utils.CopyFile(testbenchPath, mismatchDir+"/testbench.sv"); err != nil {
			f.debug.Error("Failed to copy testbench file %s to mismatch directory %s: %v", testbenchPath, mismatchDir, err)
		}
		f.debug.Debug("Test files copied to mismatch directory %s", mismatchDir)
	}
	os.RemoveAll(testDir)
	f.stats.AddMismatch(testCase)
}

func (f *Fuzzer) handleCompilationMismatch(
	workerID string, // This is the workerCompleteID from performWorkerAttempt
	workerModule *verilog.Module,
	compilationErr error,
) {
	f.debug.Error(
		"[%s] Handling compilation mismatch for module %s: %v",
		workerID,
		workerModule.Name,
		compilationErr,
	)

	// Reconstruct workerDir from workerID, as workerID is the identifier used when setting up the worker's directory.
	workerDir := filepath.Join(utils.TMP_DIR, workerID)

	// Sanitize module name and workerID for use in directory/file names
	safeModuleName := strings.ReplaceAll(workerModule.Name, "/", "_")
	safeModuleName = strings.ReplaceAll(safeModuleName, ".", "_")
	safeWorkerID := strings.ReplaceAll(workerID, "/", "_")
	safeWorkerID = strings.ReplaceAll(safeWorkerID, ".", "_")

	mismatchDirName := fmt.Sprintf("comp_mismatch_%s_%s", safeModuleName, safeWorkerID)
	mismatchDir := filepath.Join(utils.MISMATCHES_DIR, mismatchDirName)

	if err := os.MkdirAll(mismatchDir, 0o755); err != nil {
		f.debug.Error(
			"[%s] Failed to create compilation mismatch directory %s: %v",
			workerID,
			mismatchDir,
			err,
		)
		// If directory creation fails, we can't save files, but still record the stat.
	} else {
		f.debug.Info("[%s] Saving compilation failure artifacts to %s", workerID, mismatchDir)

		// 1. Copy the Verilog source file that failed compilation.
		// This file is located in workerDir (e.g., utils.TMP_DIR/worker_XYZ/f.svFile.Name).
		srcVerilogFile := filepath.Join(workerDir, f.svFile.Name)
		destVerilogFile := filepath.Join(mismatchDir, f.svFile.Name)
		if err := utils.CopyFile(srcVerilogFile, destVerilogFile); err != nil {
			f.debug.Error("[%s] Failed to copy Verilog file %s to %s: %v", workerID, srcVerilogFile, mismatchDir, err)
		} else {
			f.debug.Debug("[%s] Copied Verilog file %s to %s", workerID, srcVerilogFile, mismatchDir)
		}

		// 2. Copy the testbench file.
		// Testbenches are generated in workerDir before the compilation attempt.
		// Assuming "testbench.sv" is the standard name, as implied by handleMismatch.
		srcTestbenchFile := filepath.Join(workerDir, "testbench.sv")
		if _, statErr := os.Stat(srcTestbenchFile); statErr == nil { // Check if testbench file exists
			destTestbenchFile := filepath.Join(mismatchDir, "testbench.sv")
			if err := utils.CopyFile(srcTestbenchFile, destTestbenchFile); err != nil {
				f.debug.Error("[%s] Failed to copy testbench file %s to %s: %v", workerID, srcTestbenchFile, mismatchDir, err)
			} else {
				f.debug.Debug("[%s] Copied testbench file %s to %s", workerID, srcTestbenchFile, mismatchDir)
			}
		} else {
			f.debug.Warn("[%s] Testbench file %s not found in %s (error: %v), skipping copy.", workerID, "testbench.sv", workerDir, statErr)
		}

		// 3. Write a summary file with the error details.
		summaryFileName := fmt.Sprintf("summary_comp_mismatch_%s_%s.txt", safeModuleName, safeWorkerID)
		summaryPath := filepath.Join(mismatchDir, summaryFileName)
		summaryContent := fmt.Sprintf(
			"Compilation Mismatch Report\n\n"+
				"Worker ID: %s\n"+
				"Module: %s\n"+
				"Verilog File Base Name: %s\n\n"+ // This is the f.svFile.Name, which was copied to workerDir and compiled
				"Error Details:\n%s\n",
			workerID,
			workerModule.Name,
			f.svFile.Name,
			compilationErr.Error(),
		)

		if err := utils.WriteFileContent(summaryPath, summaryContent); err != nil {
			f.debug.Error("[%s] Failed to write compilation mismatch summary to %s: %v", workerID, summaryPath, err)
		} else {
			f.debug.Debug("[%s] Compilation mismatch summary written to %s", workerID, summaryPath)
		}
	}

	f.stats.AddCompilationMismatch()
}
