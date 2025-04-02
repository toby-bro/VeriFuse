package simulator

import (
	"fmt"
	"os"
	"time"
)

// SimResult represents the results of a simulation run
type SimResult struct {
	BranchTaken uint8
	BranchPc    uint32
}

// ReadSimResultsFromFiles reads the simulation results from specified output files
func ReadSimResultsFromFiles(takenPath, targetPath string) (SimResult, error) {
	// Try to read the taken.hex file, with retries
	var taken []byte
	var err error

	// Retry a few times to handle any delays in file creation
	for retries := 0; retries < 5; retries++ {
		taken, err = os.ReadFile(takenPath)
		if err == nil && len(taken) > 0 {
			break
		}
		time.Sleep(10 * time.Millisecond)
	}

	if err != nil || len(taken) == 0 {
		return SimResult{}, fmt.Errorf("failed to read taken file %s: %v", takenPath, err)
	}

	// Try to read the target.hex file, with retries
	var target []byte
	for retries := 0; retries < 5; retries++ {
		target, err = os.ReadFile(targetPath)
		if err == nil && len(target) > 0 {
			break
		}
		time.Sleep(10 * time.Millisecond)
	}

	if err != nil || len(target) == 0 {
		return SimResult{}, fmt.Errorf("failed to read target file %s: %v", targetPath, err)
	}

	// Parse the results
	var result SimResult

	// More robust parsing of the taken bit - handle both binary and decimal
	result.BranchTaken = 0
	if len(taken) > 0 {
		if taken[0] == '1' {
			result.BranchTaken = 1
		} else if taken[0] != '0' {
			// If it's not 0 or 1, try parsing as an integer
			var takenVal int
			if _, err := fmt.Sscanf(string(taken), "%d", &takenVal); err == nil && takenVal > 0 {
				result.BranchTaken = 1
			}
		}
	}

	// More robust parsing of the hex target - handle both with and without leading zeros
	var targetVal uint32
	if _, err = fmt.Sscanf(string(target), "%x", &targetVal); err != nil {
		return SimResult{}, fmt.Errorf("failed to parse target value '%s': %v", string(target), err)
	}
	result.BranchPc = targetVal

	return result, nil
}

// VerifyOutputFiles ensures both output files exist and are non-empty
func VerifyOutputFiles(takenPath, targetPath string) error {
	for retry := 0; retry < 3; retry++ {
		takenStat, takenErr := os.Stat(takenPath)
		targetStat, targetErr := os.Stat(targetPath)

		if takenErr == nil && targetErr == nil &&
			takenStat.Size() > 0 && targetStat.Size() > 0 {
			return nil
		}

		// Wait a bit and retry
		time.Sleep(20 * time.Millisecond)
	}

	return fmt.Errorf("output files not created properly: %s, %s", takenPath, targetPath)
}
