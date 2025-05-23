package fuzz

import (
	"fmt"
	"os"
	"path/filepath"
	"sort" // Added for sorting simulator names
	"strings"
	"time"

	"github.com/toby-bro/pfuzz/internal/verilog"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

var (
	SKIP_X_OUTPUTS bool = true
	SKIP_Z_OUTPUTS bool = false
)

func compareOutputValues(ivValue, vlValue string) bool {
	ivNorm := strings.TrimSpace(strings.ToLower(ivValue))
	vlNorm := strings.TrimSpace(strings.ToLower(vlValue))
	if SKIP_X_OUTPUTS && (strings.Contains(ivNorm, "x") ||
		strings.Contains(vlNorm, "x")) {
		return true
	}
	if SKIP_Z_OUTPUTS && (strings.Contains(ivNorm, "z") ||
		strings.Contains(vlNorm, "z")) {
		return true
	}
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

func replaceXandZwithZero(value string) string {
	// Replace 'x' and 'z' with '0'
	value = strings.ReplaceAll(value, "x", "0")
	value = strings.ReplaceAll(value, "z", "0")
	// Replace 'X' and 'Z' with '0'
	value = strings.ReplaceAll(value, "X", "0")
	value = strings.ReplaceAll(value, "Z", "0")
	return value
}

func cleanAllOutputValues(results map[string]map[string]string) {
	for simName, simResultMap := range results {
		for portName, value := range simResultMap {
			results[simName][portName] = replaceXandZwithZero(value)
		}
	}
}

func (sch *Scheduler) compareAllResults(
	results map[string]map[string]string,
) (bool, map[string]string) {
	mismatchFound := false
	mismatchDetails := make(map[string]string)

	if !SKIP_X_OUTPUTS && !SKIP_Z_OUTPUTS {
		cleanAllOutputValues(results)
	}

	simNames := make([]string, 0, len(results))
	for simName := range results {
		simNames = append(simNames, simName)
	}
	sort.Strings(simNames)

	allPorts := make(map[string]bool)
	for _, simResultMap := range results {
		for portName := range simResultMap {
			allPorts[portName] = true
		}
	}

	for portName := range allPorts {
		portReportEntries := make(map[string]string)
		actualValuesPresent := []string{}
		simsHavingThePortCount := 0

		for _, simName := range simNames {
			simResultMap, simExists := results[simName]
			if !simExists {
				portReportEntries[simName] = "SIM_DATA_MISSING"
				continue
			}
			if value, found := simResultMap[portName]; found {
				portReportEntries[simName] = value
				actualValuesPresent = append(actualValuesPresent, value)
				simsHavingThePortCount++
			} else {
				portReportEntries[simName] = "MISSING"
			}
		}

		isThisPortMismatch := false
		if simsHavingThePortCount > 0 && simsHavingThePortCount < len(simNames) {
			isThisPortMismatch = true
		} else if simsHavingThePortCount >= 2 {
			refValue := actualValuesPresent[0]
			for i := 1; i < len(actualValuesPresent); i++ {
				if !compareOutputValues(refValue, actualValuesPresent[i]) {
					isThisPortMismatch = true
					break
				}
			}
		}

		if isThisPortMismatch {
			mismatchFound = true
			detailParts := make([]string, 0, len(simNames))
			for _, simName := range simNames {
				detailParts = append(
					detailParts,
					fmt.Sprintf("%s=%s", simName, portReportEntries[simName]),
				)
			}
			mismatchDetails[portName] = strings.Join(detailParts, ", ")
			sch.debug.Warn("Mismatch for port %s: %s", portName, mismatchDetails[portName])
		}
	}

	if mismatchFound {
		var simNamesStr string
		if len(simNames) > 0 {
			simNamesStr = strings.Join(simNames, ", ")
		} else {
			sch.debug.Error("No simulator names found in results map")
		}
		sch.debug.Debug(
			"Comparison across %s found mismatches: %v",
			simNamesStr,
			mismatchDetails,
		)
	}

	return mismatchFound, mismatchDetails
}

func (sch *Scheduler) handleMismatch(
	testIndex int,
	testDir string,
	testCase map[string]string,
	mismatchDetails map[string]string,
	workerModule *verilog.Module,
) {
	sch.stats.AddMismatch(testCase)
	sch.debug.Info(
		"[%s] Mismatch FOUND in test %d for module %s%s",
		filepath.Base(testDir),
		testIndex,
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
	mismatchInstanceName := fmt.Sprintf("mismatch_test_%d_time_%d",
		testIndex, time.Now().UnixNano())
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
