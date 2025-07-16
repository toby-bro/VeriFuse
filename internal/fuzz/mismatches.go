package fuzz

import (
	"fmt"
	"path/filepath"
	"sort" // Added for sorting simulator names
	"strings"

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

func (sch *Scheduler) handleMismatch(
	testIndex int,
	testDir string,
	testCase map[*verilog.Port]string,
	mismatchDetails map[*verilog.Port]string,
	workerModule *verilog.Module,
) {
	sch.logMismatchInfo(testIndex, testDir, testCase, mismatchDetails, workerModule)
	workerDir := filepath.Dir(testDir)
	mismatchDir := filepath.Join(utils.MISMATCHES_DIR, filepath.Base(workerDir))

	utils.EnsureDir(mismatchDir)
	if err := utils.EnsureDir(mismatchDir); err != nil {
		sch.debug.Error("Failed to create mismatch directory: %v", err)
		return
	}

	if err := utils.CopyDirWithDepth(workerDir, mismatchDir, 0); err != nil {
		sch.debug.Error("Failed to copy worker directory: %v", err)
	}
	if err := utils.CopyDirWithDepth(testDir, filepath.Join(mismatchDir, filepath.Base(testDir)), 0); err != nil {
		sch.debug.Error("Failed to copy test directory: %v", err)
	}

	sch.writeMismatchSummary(testIndex, mismatchDir, testCase, mismatchDetails)

	sch.debug.Debug("Mismatch artifacts for test %d saved to %s", testIndex, mismatchDir)
}
