package fuzz

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"time"

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

// comparePairResults compares results from two simulators.
func (sch *Scheduler) comparePairResults(
	resultsA, resultsB map[string]string,
	nameA, nameB string,
) (bool, map[string]string) {
	mismatch := false
	mismatchDetails := make(map[string]string) // portName -> "SimA=valA, SimB=valB"

	processedPorts := make(map[string]bool)

	for portName, valA := range resultsA {
		processedPorts[portName] = true
		valB, existsB := resultsB[portName]
		if !existsB {
			mismatch = true
			mismatchDetails[portName] = fmt.Sprintf("%s=%s, %s=MISSING", nameA, valA, nameB)
			sch.debug.Warn(
				"Mismatch: Port %s found in %s but MISSING in %s",
				portName,
				nameA,
				nameB,
			)
			continue
		}
		if !compareOutputValues(valA, valB) { // Uses existing low-level compareOutputValues
			mismatch = true
			mismatchDetails[portName] = fmt.Sprintf(
				"%s=%s, %s=%s",
				nameA, valA,
				nameB, valB,
			)
			sch.debug.Warn("Mismatch: Port %s, %s=%s, %s=%s", portName, nameA, valA, nameB, valB)
		}
	}

	for portName, valB := range resultsB {
		if _, processed := processedPorts[portName]; processed {
			continue // Already compared from resultsA's perspective
		}
		// This port exists in B but not in A (or was not in resultsA map)
		mismatch = true
		mismatchDetails[portName] = fmt.Sprintf("%s=MISSING, %s=%s", nameA, nameB, valB)
		sch.debug.Warn("Mismatch: Port %s MISSING in %s but found in %s", portName, nameA, nameB)
	}

	if mismatch {
		sch.debug.Debug(
			"Comparison between %s and %s found mismatches: %v",
			nameA,
			nameB,
			mismatchDetails,
		)
	}
	return mismatch, mismatchDetails
}

func (sch *Scheduler) handleMismatch(
	testIndex int,
	testDir string,
	testCase map[string]string,
	mismatchDetails map[string]string,
	workerModule *verilog.Module,
	simNameA string,
	simNameB string,
) {
	sch.stats.AddMismatch(testCase) // Moved here from runSingleTest
	sch.debug.Error(                // Changed from Info to Error for more visibility
		"[%s] Mismatch FOUND in test %d between %s and %s for module %s",
		filepath.Base(testDir), // Use base name of testDir for brevity
		testIndex,
		simNameA,
		simNameB,
		workerModule.Name,
	)
	sch.debug.Info("Inputs for test %d:", testIndex)
	for portName, value := range testCase {
		sch.debug.Info("  %s = %s", portName, value)
	}
	sch.debug.Info("Mismatched outputs:")
	for portName, detail := range mismatchDetails {
		sch.debug.Info("  %s: %s", portName, detail)
	}
	// Create a unique directory for this mismatch instance
	mismatchInstanceName := fmt.Sprintf("mismatch_%s_vs_%s_test_%d_time_%d",
		simNameA, simNameB, testIndex, time.Now().UnixNano())
	mismatchDir := filepath.Join(utils.MISMATCHES_DIR, mismatchInstanceName)

	if err := os.MkdirAll(mismatchDir, 0o755); err != nil {
		sch.debug.Error("Failed to create mismatch directory %s: %v", mismatchDir, err)
	} else {
		// Copy all the files from the test directory to the mismatch directory
		sch.debug.Debug("Copying test files to mismatch directory %s", mismatchDir)
		if err := utils.CopyDir(testDir, mismatchDir); err != nil {
			sch.debug.Error("Failed to copy test files to mismatch directory %s: %v", mismatchDir, err)
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
		sch.debug.Debug("Writing mismatch summary to %s", summaryPath)
		err := utils.WriteFileContent(summaryPath, fileContent)
		if err != nil {
			sch.debug.Error("Failed to write mismatch summary to %s: %v", summaryPath, err)
		}
		// also copy the file that was tested and the testbench
		testFilePath := filepath.Join(testDir, "../")
		testFilePath = filepath.Join(testFilePath, sch.svFile.Name)
		if err := utils.CopyFile(testFilePath, mismatchDir+"/"+sch.svFile.Name); err != nil {
			sch.debug.Error("Failed to copy test file %s to mismatch directory %s: %v", testFilePath, mismatchDir, err)
		}
		testbenchPath := filepath.Join(testDir, "../testbench.sv")
		if err := utils.CopyFile(testbenchPath, mismatchDir+"/testbench.sv"); err != nil {
			sch.debug.Error("Failed to copy testbench file %s to mismatch directory %s: %v", testbenchPath, mismatchDir, err)
		}
		// If using CXXRTL, copy the CXXRTL testbench as well
		sourceCppTestbenchPath := filepath.Join(testDir, "../testbench.cpp")
		if err := utils.CopyFile(sourceCppTestbenchPath, mismatchDir+"/testbench.cpp"); err != nil {
			sch.debug.Error("Failed to copy CXXRTL testbench %s to %s: %v", sourceCppTestbenchPath, mismatchDir, err)
		}
	}

	sch.debug.Debug("Mismatch artifacts for test %d saved to %s", testIndex, mismatchDir)
}

func (sch *Scheduler) handleCompilationMismatch(
	workerID string, // This is the workerCompleteID from performWorkerAttempt
	workerModule *verilog.Module,
	compilationErr error,
) {
	sch.debug.Error(
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
		sch.debug.Error(
			"[%s] Failed to create compilation mismatch directory %s: %v",
			workerID,
			mismatchDir,
			err,
		)
		// If directory creation fails, we can't save files, but still record the stat.
	} else {
		sch.debug.Info("[%s] Saving compilation failure artifacts to %s", workerID, mismatchDir)

		// 1. Copy the Verilog source file that failed compilation.
		// This file is located in workerDir (e.g., utils.TMP_DIR/worker_XYZ/f.svFile.Name).
		srcVerilogFile := filepath.Join(workerDir, sch.svFile.Name)
		destVerilogFile := filepath.Join(mismatchDir, sch.svFile.Name)
		if err := utils.CopyFile(srcVerilogFile, destVerilogFile); err != nil {
			sch.debug.Error("[%s] Failed to copy Verilog file %s to %s: %v", workerID, srcVerilogFile, mismatchDir, err)
		} else {
			sch.debug.Debug("[%s] Copied Verilog file %s to %s", workerID, srcVerilogFile, mismatchDir)
		}

		// 2. Copy the testbench file.
		// Testbenches are generated in workerDir before the compilation attempt.
		// Assuming "testbench.sv" is the standard name, as implied by handleMismatch.
		srcTestbenchFile := filepath.Join(workerDir, "testbench.sv")
		if _, statErr := os.Stat(srcTestbenchFile); statErr == nil { // Check if testbench file exists
			destTestbenchFile := filepath.Join(mismatchDir, "testbench.sv")
			if err := utils.CopyFile(srcTestbenchFile, destTestbenchFile); err != nil {
				sch.debug.Error("[%s] Failed to copy testbench file %s to %s: %v", workerID, srcTestbenchFile, mismatchDir, err)
			} else {
				sch.debug.Debug("[%s] Copied testbench file %s to %s", workerID, srcTestbenchFile, mismatchDir)
			}
		} else {
			sch.debug.Warn("[%s] Testbench file %s not found in %s (error: %v), skipping copy.", workerID, "testbench.sv", workerDir, statErr)
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
			sch.svFile.Name,
			compilationErr.Error(),
		)

		if err := utils.WriteFileContent(summaryPath, summaryContent); err != nil {
			sch.debug.Error("[%s] Failed to write compilation mismatch summary to %s: %v", workerID, summaryPath, err)
		} else {
			sch.debug.Debug("[%s] Compilation mismatch summary written to %s", workerID, summaryPath)
		}
	}

	sch.stats.AddCompilationMismatch()
}
