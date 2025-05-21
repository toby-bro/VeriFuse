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

		// Copy relevant files using glob patterns, excluding 'obj_dir'
		sch.debug.Info("Copying additional files from source tree to mismatch directory %s", mismatchDir)
		globSrcDir := filepath.Join(testDir, "..")
		patterns := []string{"*.sv", "*.cc", "*.hex"} // Assuming .hex for user's .:whex
		excludeDirName := "obj_dir"

		walkErr := filepath.Walk(globSrcDir, func(currentPath string, info os.FileInfo, walkErrIn error) error {
			if walkErrIn != nil {
				// Error accessing path (e.g. permission denied), log and decide how to handle.
				// Depending on the error, we might want to skip this path or stop the walk.
				// For now, log and skip the problematic path.
				sch.debug.Warn("Error accessing path %s during walk: %v. Skipping.", currentPath, walkErrIn)
				if info != nil && info.IsDir() {
					return filepath.SkipDir // If it's a directory we can't access, skip it.
				}
				return nil // If it's a file or other error, just skip this entry.
			}

			relPath, err := filepath.Rel(globSrcDir, currentPath)
			if err != nil {
				sch.debug.Error("Failed to get relative path for %s (base %s): %v", currentPath, globSrcDir, err)
				return err // This is unexpected, propagate error.
			}

			// Check if any part of the path contains the excluded directory name.
			pathSegments := strings.Split(relPath, string(filepath.Separator))
			for _, segment := range pathSegments {
				if segment == excludeDirName {
					if info.IsDir() {
						sch.debug.Debug("Skipping excluded directory: %s", currentPath)
						return filepath.SkipDir
					}
					// File is within an excluded directory's path.
					sch.debug.Debug("Skipping file in excluded path: %s", currentPath)
					return nil
				}
			}

			if info.IsDir() {
				return nil // It's a directory, but not excluded. Continue walking.
			}

			// Check if the file matches any of the specified patterns.
			matchedPattern := false
			for _, pattern := range patterns {
				if matched, _ := filepath.Match(pattern, filepath.Base(currentPath)); matched {
					matchedPattern = true
					break
				}
			}

			if matchedPattern {
				destPath := filepath.Join(mismatchDir, relPath)

				// Ensure the destination directory structure exists.
				if err := os.MkdirAll(filepath.Dir(destPath), 0o755); err != nil {
					sch.debug.Error("Failed to create directory for %s: %v", destPath, err)
					return nil // Continue with other files.
				}

				// Copy the file.
				sch.debug.Debug("Copying matched file %s to %s", currentPath, destPath)
				if err := utils.CopyFile(currentPath, destPath); err != nil {
					sch.debug.Error("Failed to copy file %s to %s: %v", currentPath, destPath, err)
					// Continue with other files.
				}
			}
			return nil
		})

		if walkErr != nil {
			sch.debug.Error("Error during glob-based file copying: %v", walkErr)
		}
	}

	sch.debug.Debug("Mismatch artifacts for test %d saved to %s", testIndex, mismatchDir)
}
