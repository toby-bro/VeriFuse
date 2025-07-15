package fuzz

import (
	"fmt"
	"os"
	"path/filepath"
	"sort" // Added for sorting simulator names
	"strings"
	"time"

	"github.com/toby-bro/pfuzz/internal/synth"
	"github.com/toby-bro/pfuzz/pkg/utils"
	"github.com/toby-bro/pfuzz/pkg/verilog"
)

var (
	SKIP_X_OUTPUTS = true
	SKIP_Z_OUTPUTS = true
)

// compareOutputValues compares two output values, ivValue and vlValue.
// It returns true if they are considered equivalent, false otherwise.
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

// replaceXandZwithZero replaces all occurrences of 'x', 'z', 'X', and 'Z' in the
// given value with '0'. This is useful for normalizing output values before comparison.
func replaceXandZwithZero(value string) string {
	// Replace 'x' and 'z' with '0'
	value = strings.ReplaceAll(value, "x", "0")
	value = strings.ReplaceAll(value, "z", "0")
	// Replace 'X' and 'Z' with '0'
	value = strings.ReplaceAll(value, "X", "0")
	value = strings.ReplaceAll(value, "Z", "0")
	return value
}

// cleanAllOutputValues replaces 'x' and 'z' in all output values with '0'
// in the results map. This is useful for normalizing output values before comparison.
func cleanAllOutputValues(results map[*SimInstance]map[*verilog.Port]string) {
	for simInstance, simResultMap := range results {
		for port, value := range simResultMap {
			results[simInstance][port] = replaceXandZwithZero(value)
		}
	}
}

// removeSynthesizers removes all SimInstances
// from the results map where the Synthesizer type is not None.
func removeSynthesizers(results map[*SimInstance]map[*verilog.Port]string) {
	var toDelete []*SimInstance
	for simInstance := range results {
		if simInstance.Synthesizer != synth.None {
			toDelete = append(toDelete, simInstance)
		}
	}
	for _, simInstance := range toDelete {
		delete(results, simInstance)
	}
}

func (sch *Scheduler) compareAllResults(
	results map[*SimInstance]map[*verilog.Port]string,
) (bool, map[*verilog.Port]string) {
	mismatchFound := false
	mismatchDetails := make(map[*verilog.Port]string)

	xorzPresent := false
	for _, simResultMap := range results {
		for _, value := range simResultMap {
			if strings.Contains(value, "x") || strings.Contains(value, "z") {
				xorzPresent = true
				break
			}
		}
	}

	if !SKIP_X_OUTPUTS && !SKIP_Z_OUTPUTS && xorzPresent {
		cleanAllOutputValues(results)
	}

	// if x or z is present in any output we exclude all the SimInstances where the synth.Type is not None as they can do whatever they want
	if xorzPresent {
		removeSynthesizers(results)
	}

	sims := make([]*SimInstance, 0, len(results))
	for sim := range results {
		sims = append(sims, sim)
	}
	sort.Slice(sims, func(i, j int) bool {
		if sims[i].Simulator.Type() == sims[j].Simulator.Type() {
			return sims[i].Synthesizer < sims[j].Synthesizer
		}
		return sims[i].Simulator.Type() < sims[j].Simulator.Type()
	})

	allPorts := make(map[*verilog.Port]bool)
	for _, simResultMap := range results {
		for port := range simResultMap {
			allPorts[port] = true
		}
	}

	for port := range allPorts {
		portReportEntries := make(map[*SimInstance]string)
		actualValuesPresent := []string{}
		simsHavingThePortCount := 0

		for _, sim := range sims {
			simResultMap, simExists := results[sim]
			if !simExists {
				portReportEntries[sim] = "SIM_DATA_MISSING"
				sch.debug.Warn(
					"Simulator %s not found in results map for port %s",
					sim.String(),
					port.Name,
				)
				continue
			}
			if value, found := simResultMap[port]; found {
				portReportEntries[sim] = value
				actualValuesPresent = append(actualValuesPresent, value)
				simsHavingThePortCount++
			} else {
				sch.debug.Warn(
					"Port %s not found in simulator %s results map",
					port.Name,
					sim.String(),
				)
				portReportEntries[sim] = "MISSING"
			}
		}

		isThisPortMismatch := false
		if simsHavingThePortCount > 0 && simsHavingThePortCount < len(sims) {
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
			detailParts := make([]string, 0, len(sims))
			for _, sim := range sims {
				detailParts = append(
					detailParts,
					fmt.Sprintf("%s=%s", sim.String(), portReportEntries[sim]),
				)
			}
			mismatchDetails[port] = strings.Join(detailParts, ", ")
			sch.debug.Warn("Mismatch for port %s: %s", port.Name, mismatchDetails[port])
		}
	}

	if mismatchFound {
		var simNamesStr string
		if len(sims) > 0 {
			simNamesStr = "[" + sims[0].String()
			for i := 1; i < len(sims); i++ {
				simNamesStr += ", " + sims[i].String()
			}
			simNamesStr += "]"
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

// logMismatchInfo logs the mismatch information and updates statistics
func (sch *Scheduler) logMismatchInfo(
	testIndex int,
	testDir string,
	testCase map[*verilog.Port]string,
	mismatchDetails map[*verilog.Port]string,
	workerModule *verilog.Module,
) {
	sch.stats.AddMismatch(testCase)
	sch.debug.Info(
		"[%s] Mismatch FOUND in test %d for module %s",
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
}

// createMismatchDirectory creates a unique directory for storing mismatch artifacts
func (sch *Scheduler) createMismatchDirectory(testIndex int) (string, error) {
	mismatchInstanceName := fmt.Sprintf("mismatch_test_%d_time_%d",
		testIndex, time.Now().UnixNano())
	mismatchDir := filepath.Join(utils.MISMATCHES_DIR, mismatchInstanceName)

	if err := os.MkdirAll(mismatchDir, 0o755); err != nil {
		sch.debug.Error("Failed to create mismatch directory %s: %v", mismatchDir, err)
		return "", err
	}
	return mismatchDir, nil
}

// copyTestFiles copies files from the test directory to the mismatch directory
func (sch *Scheduler) copyTestFiles(testDir string, mismatchDir string) {
	sch.debug.Debug(
		"Copying files from test directory %s to mismatch directory %s",
		testDir,
		mismatchDir,
	)
	files, err := os.ReadDir(testDir)
	if err != nil {
		sch.debug.Error("Failed to read test directory %s: %v", testDir, err)
		return
	}

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

// writeMismatchSummary creates and writes the mismatch summary file
func (sch *Scheduler) writeMismatchSummary(
	testIndex int,
	mismatchDir string,
	testCase map[*verilog.Port]string,
	mismatchDetails map[*verilog.Port]string,
) {
	summaryPath := filepath.Join(mismatchDir, fmt.Sprintf("mismatch_%d_summary.txt", testIndex))
	fileContent := fmt.Sprintf("Test case %d\n\nInputs:\n", testIndex)

	for port, value := range testCase {
		fileContent += fmt.Sprintf("  %v = %s\n", port, value)
	}

	fileContent += "\nMismatched outputs:\n"
	for port, detail := range mismatchDetails {
		fileContent += fmt.Sprintf("  %v:\n", port)
		detailsSplit := strings.Split(detail, ", ")
		for _, part := range detailsSplit {
			fileContent += fmt.Sprintf("    %s\n", part)
		}
	}

	sch.debug.Debug("Writing mismatch summary to %s", summaryPath)
	if err := utils.WriteFileContent(summaryPath, fileContent); err != nil {
		sch.debug.Error("Failed to write mismatch summary to %s: %v", summaryPath, err)
	}
}

// copySvFile copies the main SystemVerilog file to the mismatch directory
func (sch *Scheduler) copySvFile(baseSrcDir, mismatchDir string) {
	// find all the .sv files in the base source directory
	svFiles, err := filepath.Glob(filepath.Join(baseSrcDir, "*.[svv]"))
	if err != nil {
		sch.debug.Error("Failed to find .sv files in %s: %v", baseSrcDir, err)
		return
	}
	if len(svFiles) == 0 {
		sch.debug.Warn("No .sv files found in %s. Skipping copy.", baseSrcDir)
		return
	}
	// copy all the files to the mismatch directory
	for _, svFile := range svFiles {
		destSvFile := filepath.Join(mismatchDir, filepath.Base(svFile))
		if err := utils.CopyFile(svFile, destSvFile); err != nil {
			sch.debug.Error("Failed to copy .sv file %s to %s: %v", svFile, destSvFile, err)
		} else {
			sch.debug.Debug("Copied .sv file %s to %s", svFile, destSvFile)
		}
	}
}

// copyTestbenchFile copies the testbench.sv file to the mismatch directory
func (sch *Scheduler) copyTestbenchFile(baseSrcDir, mismatchDir string) {
	sourceTestbenchPath := filepath.Join(baseSrcDir, "testbench.sv")
	destTestbenchPath := filepath.Join(mismatchDir, "testbench.sv")

	if _, statErr := os.Stat(sourceTestbenchPath); statErr == nil {
		if copyErr := utils.CopyFile(sourceTestbenchPath, destTestbenchPath); copyErr != nil {
			sch.debug.Warn(
				"Failed to copy testbench.sv %s to %s: %v",
				sourceTestbenchPath,
				destTestbenchPath,
				copyErr,
			)
		} else {
			sch.debug.Debug("Copied testbench.sv %s to %s", sourceTestbenchPath, destTestbenchPath)
		}
	} else if !os.IsNotExist(statErr) {
		sch.debug.Warn("Error stating testbench.sv %s: %v. Skipping copy.", sourceTestbenchPath, statErr)
	} else {
		sch.debug.Debug("testbench.sv %s not found. Skipping copy.", sourceTestbenchPath)
	}
}

// copyCxxrtlFiles copies CXXRTL-related files to the mismatch directory
func (sch *Scheduler) copyCxxrtlFiles(
	baseSrcDir, mismatchDir string,
	workerModule *verilog.Module,
) {
	cxxrtlDirNames := []string{"cxxrtl_sim", "cxxrtl_slang_sim"}

	for _, dirName := range cxxrtlDirNames {
		cxxrtlSimDir := filepath.Join(baseSrcDir, dirName)

		if _, statErr := os.Stat(cxxrtlSimDir); os.IsNotExist(statErr) {
			sch.debug.Debug("CXXRTL directory %s not found. Skipping.", cxxrtlSimDir)
			continue
		} else if statErr != nil {
			sch.debug.Warn("Error stating CXXRTL directory %s: %v. Skipping.", cxxrtlSimDir, statErr)
			continue
		}

		sch.debug.Debug("Checking for CXXRTL files in %s", cxxrtlSimDir)
		sch.copyCxxrtlTestbench(cxxrtlSimDir, mismatchDir, dirName)
		sch.copyCxxrtlModuleFile(cxxrtlSimDir, mismatchDir, dirName, workerModule)
	}
}

// copyCxxrtlTestbench copies the CXXRTL testbench.cpp file
func (sch *Scheduler) copyCxxrtlTestbench(cxxrtlSimDir, mismatchDir, dirName string) {
	sourceCppTestbenchPath := filepath.Join(cxxrtlSimDir, "testbench.cpp")
	destCppTestbenchPath := filepath.Join(mismatchDir, dirName+"_testbench.cpp")

	if _, statErr := os.Stat(sourceCppTestbenchPath); statErr == nil {
		if copyErr := utils.CopyFile(sourceCppTestbenchPath, destCppTestbenchPath); copyErr != nil {
			sch.debug.Error(
				"Failed to copy CXXRTL testbench %s to %s: %v",
				sourceCppTestbenchPath,
				destCppTestbenchPath,
				copyErr,
			)
		} else {
			sch.debug.Debug("Copied CXXRTL testbench.cpp %s to %s", sourceCppTestbenchPath, destCppTestbenchPath)
		}
	} else if !os.IsNotExist(statErr) {
		sch.debug.Warn("Could not stat CXXRTL testbench %s: %v. Skipping copy.", sourceCppTestbenchPath, statErr)
	}
}

// copyCxxrtlModuleFile copies the CXXRTL module .cc file
func (sch *Scheduler) copyCxxrtlModuleFile(
	cxxrtlSimDir, mismatchDir, dirName string,
	workerModule *verilog.Module,
) {
	if workerModule == nil || workerModule.Name == "" {
		sch.debug.Warn(
			"workerModule or workerModule.Name is not set. Skipping copy of CXXRTL module .cc file for %s.",
			dirName,
		)
		return
	}

	cxxrtlModuleCcFileName := workerModule.Name + ".cc"
	sourceModuleCcPath := filepath.Join(cxxrtlSimDir, cxxrtlModuleCcFileName)
	destModuleCcPath := filepath.Join(
		mismatchDir,
		fmt.Sprintf("%s_%s", dirName, cxxrtlModuleCcFileName),
	)

	if _, statErr := os.Stat(sourceModuleCcPath); statErr == nil {
		if copyErr := utils.CopyFile(sourceModuleCcPath, destModuleCcPath); copyErr != nil {
			sch.debug.Error(
				"Failed to copy CXXRTL module .cc file %s to %s: %v",
				sourceModuleCcPath,
				destModuleCcPath,
				copyErr,
			)
		} else {
			sch.debug.Debug("Copied CXXRTL module .cc file %s to %s", sourceModuleCcPath, destModuleCcPath)
		}
	} else if !os.IsNotExist(statErr) {
		sch.debug.Warn("Could not stat CXXRTL module .cc file %s: %v. Skipping copy.", sourceModuleCcPath, statErr)
	}
}

// copySpecificFiles copies specific files relevant to the test case
func (sch *Scheduler) copySpecificFiles(testDir, mismatchDir string, workerModule *verilog.Module) {
	sch.debug.Info("Copying specific files for mismatch in %s", mismatchDir)

	// Base directory for source files (design, testbench, etc.)
	// testDir is like .../work_dir/test_N. Its parent is work_dir.
	baseSrcDir := filepath.Join(testDir, "..")

	sch.copySvFile(baseSrcDir, mismatchDir)
	sch.copyTestbenchFile(baseSrcDir, mismatchDir)
	sch.copyCxxrtlFiles(baseSrcDir, mismatchDir, workerModule)
}

func (sch *Scheduler) handleMismatch(
	testIndex int,
	testDir string,
	testCase map[*verilog.Port]string,
	mismatchDetails map[*verilog.Port]string,
	workerModule *verilog.Module,
) {
	sch.logMismatchInfo(testIndex, testDir, testCase, mismatchDetails, workerModule)

	mismatchDir, err := sch.createMismatchDirectory(testIndex)
	if err != nil {
		return
	}

	sch.copyTestFiles(testDir, mismatchDir)
	sch.writeMismatchSummary(testIndex, mismatchDir, testCase, mismatchDetails)
	sch.copySpecificFiles(testDir, mismatchDir, workerModule)

	sch.debug.Debug("Mismatch artifacts for test %d saved to %s", testIndex, mismatchDir)
}
