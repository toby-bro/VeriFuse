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
		// Copy files from the test directory to the mismatch directory, excluding subdirectories
		sch.debug.Debug("Copying files from test directory %s to mismatch directory %s", testDir, mismatchDir)
		files, err := os.ReadDir(testDir)
		if err != nil {
			sch.debug.Error("Failed to read test directory %s: %v", testDir, err)
		} else {
			for _, file := range files {
				if !file.IsDir() {
					srcPath := filepath.Join(testDir, file.Name())
					destPath := filepath.Join(mismatchDir, file.Name())
					if err := utils.CopyFile(srcPath, destPath); err != nil {
						sch.debug.Error("Failed to copy file %s to %s: %v", srcPath, destPath, err)
					}
				}
			}
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
		// err is already declared above, so use = instead of :=
		err = utils.WriteFileContent(summaryPath, fileContent)
		if err != nil {
			sch.debug.Error("Failed to write mismatch summary to %s: %v", summaryPath, err)
		}

		// Copy specific files relevant to the test case
		sch.debug.Info("Copying specific files for mismatch in %s", mismatchDir)

		// Base directory for source files (design, testbench, etc.)
		// testDir is like .../work_dir/test_N. Its parent is work_dir.
		baseSrcDir := filepath.Join(testDir, "..")

		// 1. Copy the main SV file (original design file)
		// Assuming sch.svFile.Name is the simple filename, e.g., "my_module.sv"
		// Also assuming sch.svFile is a pointer and might be nil.
		if sch.svFile != nil && sch.svFile.Name != "" {
			originalSvFileName := sch.svFile.Name
			sourceSvFilePath := filepath.Join(baseSrcDir, originalSvFileName)
			destSvFilePath := filepath.Join(mismatchDir, originalSvFileName)

			// Check if source file exists before attempting to copy
			if _, statErr := os.Stat(sourceSvFilePath); statErr == nil {
				if copyErr := utils.CopyFile(sourceSvFilePath, destSvFilePath); copyErr != nil {
					sch.debug.Warn("Failed to copy original SV file %s to %s: %v", sourceSvFilePath, destSvFilePath, copyErr)
				} else {
					sch.debug.Debug("Copied original SV file %s to %s", sourceSvFilePath, destSvFilePath)
				}
			} else if !os.IsNotExist(statErr) {
				// Log if stat failed for a reason other than "not exist"
				sch.debug.Warn("Error stating original SV file %s: %v. Skipping copy.", sourceSvFilePath, statErr)
			} else {
				// File does not exist, log as debug/info as it might be expected in some setups
				sch.debug.Info("Original SV file %s not found. Skipping copy.", sourceSvFilePath)
			}
		} else {
			sch.debug.Warn("sch.svFile or sch.svFile.Name is not set. Skipping copy of original SV file.")
		}

		// 2. Copy the main testbench.sv
		sourceTestbenchPath := filepath.Join(baseSrcDir, "testbench.sv")
		destTestbenchPath := filepath.Join(mismatchDir, "testbench.sv")
		if _, statErr := os.Stat(sourceTestbenchPath); statErr == nil {
			if copyErr := utils.CopyFile(sourceTestbenchPath, destTestbenchPath); copyErr != nil {
				sch.debug.Warn("Failed to copy testbench.sv %s to %s: %v", sourceTestbenchPath, destTestbenchPath, copyErr)
			} else {
				sch.debug.Debug("Copied testbench.sv %s to %s", sourceTestbenchPath, destTestbenchPath)
			}
		} else if !os.IsNotExist(statErr) {
			sch.debug.Warn("Error stating testbench.sv %s: %v. Skipping copy.", sourceTestbenchPath, statErr)
		} else {
			sch.debug.Debug("testbench.sv %s not found. Skipping copy.", sourceTestbenchPath)
		}

		// 3. Attempt to copy CXXRTL specific files if they exist.
		// These are typically in a 'cxxrtl_sim' or 'cxxrtl_slang_sim' subdirectory within baseSrcDir.
		cxxrtlDirNames := []string{"cxxrtl_sim", "cxxrtl_slang_sim"}

		for _, dirName := range cxxrtlDirNames {
			cxxrtlSimDir := filepath.Join(baseSrcDir, dirName)
			// Check if this specific cxxrtl directory exists
			if _, statErr := os.Stat(cxxrtlSimDir); os.IsNotExist(statErr) {
				sch.debug.Debug("CXXRTL directory %s not found. Skipping.", cxxrtlSimDir)
				continue // Try the next directory name
			} else if statErr != nil {
				sch.debug.Warn("Error stating CXXRTL directory %s: %v. Skipping.", cxxrtlSimDir, statErr)
				continue // Try the next directory name
			}

			sch.debug.Debug("Checking for CXXRTL files in %s", cxxrtlSimDir)

			// CXXRTL testbench.cpp
			sourceCppTestbenchPath := filepath.Join(cxxrtlSimDir, "testbench.cpp")
			destCppTestbenchPath := filepath.Join(mismatchDir, fmt.Sprintf("%s_testbench.cpp", dirName)) // Ensure unique names if both dirs exist
			if _, statErr := os.Stat(sourceCppTestbenchPath); statErr == nil {                           // File exists
				if copyErr := utils.CopyFile(sourceCppTestbenchPath, destCppTestbenchPath); copyErr != nil {
					sch.debug.Error("Failed to copy CXXRTL testbench %s to %s: %v", sourceCppTestbenchPath, destCppTestbenchPath, copyErr)
				} else {
					sch.debug.Debug("Copied CXXRTL testbench.cpp %s to %s", sourceCppTestbenchPath, destCppTestbenchPath)
				}
			} else if !os.IsNotExist(statErr) {
				sch.debug.Warn("Could not stat CXXRTL testbench %s: %v. Skipping copy.", sourceCppTestbenchPath, statErr)
			} // If os.IsNotExist(statErr), do nothing - file is optional.

			// CXXRTL module .cc file (e.g., <module_name>.cc)
			if workerModule != nil && workerModule.Name != "" {
				cxxrtlModuleCcFileName := fmt.Sprintf("%s.cc", workerModule.Name)
				sourceModuleCcPath := filepath.Join(cxxrtlSimDir, cxxrtlModuleCcFileName)
				destModuleCcPath := filepath.Join(mismatchDir, fmt.Sprintf("%s_%s", dirName, cxxrtlModuleCcFileName)) // Ensure unique names

				if _, statErr := os.Stat(sourceModuleCcPath); statErr == nil { // File exists
					if copyErr := utils.CopyFile(sourceModuleCcPath, destModuleCcPath); copyErr != nil {
						sch.debug.Error("Failed to copy CXXRTL module .cc file %s to %s: %v", sourceModuleCcPath, destModuleCcPath, copyErr)
					} else {
						sch.debug.Debug("Copied CXXRTL module .cc file %s to %s", sourceModuleCcPath, destModuleCcPath)
					}
				} else if !os.IsNotExist(statErr) {
					sch.debug.Warn("Could not stat CXXRTL module .cc file %s: %v. Skipping copy.", sourceModuleCcPath, statErr)
				} // If os.IsNotExist(statErr), do nothing.
			} else {
				sch.debug.Warn("workerModule or workerModule.Name is not set. Skipping copy of CXXRTL module .cc file for %s.", dirName)
			}
		}
	}

	sch.debug.Debug("Mismatch artifacts for test %d saved to %s", testIndex, mismatchDir)
}
