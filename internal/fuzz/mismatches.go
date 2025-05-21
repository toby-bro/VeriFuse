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
		sourceCppTestbenchPath := filepath.Join(testDir, "../cxxrtl_sim/testbench.cpp")
		if err := utils.CopyFile(sourceCppTestbenchPath, mismatchDir+"/testbench.cpp"); err != nil {
			sch.debug.Error("Failed to copy CXXRTL testbench %s to %s: %v", sourceCppTestbenchPath, mismatchDir, err)
		}
		// Copy any .cc file
		sourceCCFilePath := filepath.Join(testDir, fmt.Sprintf("../cxxrtl_sim/%s.cc", workerModule.Name))
		if err := utils.CopyFile(sourceCCFilePath, mismatchDir+"/"); err != nil {
			sch.debug.Error("Failed to copy CXXRTL .cc file %s to %s: %v", sourceCCFilePath, mismatchDir, err)
		}
	}

	sch.debug.Debug("Mismatch artifacts for test %d saved to %s", testIndex, mismatchDir)
}
