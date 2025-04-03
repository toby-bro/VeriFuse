package simulator

import (
	"fmt"
	"os"
	"sync"
	"time"
)

// Simulator defines the interface for RTL simulators
type Simulator interface {
	// Compile compiles the simulator from source files
	Compile() error

	// RunTest runs the simulator with the provided input and output files
	RunTest(inputPath, pcPath, validPath, takenPath, targetPath string) error

	// GetExecPath returns the path to the compiled simulator executable
	GetExecPath() string
}

// SimResult represents the results of a simulation run
type SimResult struct {
	BranchTaken uint8
	BranchPc    uint32
}

var fileAccessMutex sync.Mutex

// ReadSimResultsFromFiles reads the simulation results from specified output files
func ReadSimResultsFromFiles(takenPath, targetPath string) (SimResult, error) {
	var result SimResult
	var wg sync.WaitGroup
	var takenErr, targetErr error
	var taken, target []byte

	// Use goroutines to read files concurrently
	wg.Add(2)

	// Goroutine to read taken file
	go func() {
		defer wg.Done()

		// Try to read the taken.hex file with retries
		for retries := 0; retries < 10; retries++ {
			fileAccessMutex.Lock()
			taken, takenErr = os.ReadFile(takenPath)
			fileAccessMutex.Unlock()

			if takenErr == nil && len(taken) > 0 {
				break
			}

			// Exponential backoff
			waitTime := time.Duration(20*(1<<retries)) * time.Millisecond
			if waitTime > 500*time.Millisecond {
				waitTime = 500 * time.Millisecond
			}
			time.Sleep(waitTime)
		}
	}()

	// Goroutine to read target file
	go func() {
		defer wg.Done()

		// Try to read the target.hex file with retries
		for retries := 0; retries < 10; retries++ {
			fileAccessMutex.Lock()
			target, targetErr = os.ReadFile(targetPath)
			fileAccessMutex.Unlock()

			if targetErr == nil && len(target) > 0 {
				break
			}

			// Exponential backoff
			waitTime := time.Duration(20*(1<<retries)) * time.Millisecond
			if waitTime > 500*time.Millisecond {
				waitTime = 500 * time.Millisecond
			}
			time.Sleep(waitTime)
		}
	}()

	// Wait for both goroutines to finish
	wg.Wait()

	// Handle taken file errors
	if takenErr != nil || len(taken) == 0 {
		return SimResult{}, fmt.Errorf("failed to read taken file %s: %v", takenPath, takenErr)
	}

	// Parse taken value with robust error handling
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

	// Handle target file errors
	if targetErr != nil || len(target) == 0 {
		return SimResult{}, fmt.Errorf("failed to read target file %s: %v", targetPath, targetErr)
	}

	// Parse target value
	var targetVal uint32
	if _, err := fmt.Sscanf(string(target), "%x", &targetVal); err != nil {
		return SimResult{}, fmt.Errorf("failed to parse target value '%s': %v", string(target), err)
	}
	result.BranchPc = targetVal

	return result, nil
}

// VerifyOutputFiles ensures both output files exist and are non-empty using concurrent checks
func VerifyOutputFiles(takenPath, targetPath string) error {
	var wg sync.WaitGroup
	var takenOk, targetOk bool
	var takenSize, targetSize int64

	// Use goroutines to check files concurrently
	wg.Add(2)

	// Goroutine to check taken file
	go func() {
		defer wg.Done()
		for retry := 0; retry < 5; retry++ {
			fileAccessMutex.Lock()
			stat, err := os.Stat(takenPath)
			fileAccessMutex.Unlock()

			if err == nil && stat.Size() > 0 {
				takenOk = true
				takenSize = stat.Size()
				return
			}
			time.Sleep(50 * time.Millisecond)
		}
	}()

	// Goroutine to check target file
	go func() {
		defer wg.Done()
		for retry := 0; retry < 5; retry++ {
			fileAccessMutex.Lock()
			stat, err := os.Stat(targetPath)
			fileAccessMutex.Unlock()

			if err == nil && stat.Size() > 0 {
				targetOk = true
				targetSize = stat.Size()
				return
			}
			time.Sleep(50 * time.Millisecond)
		}
	}()

	// Wait for both checks to complete
	wg.Wait()

	if !takenOk || !targetOk {
		return fmt.Errorf("output files not created properly: taken=%s (%v, %d bytes), target=%s (%v, %d bytes)",
			takenPath, takenOk, takenSize, targetPath, targetOk, targetSize)
	}

	return nil
}
