package simulator

import (
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"time"
)

// Simulator defines the interface for RTL simulators
type Simulator interface {
	// Compile compiles the simulator from source files
	Compile() error

	// RunTest runs the simulator with the provided input and output files
	// inputDir is the directory containing input files
	// outputPaths maps port names to output file paths
	RunTest(inputDir string, outputPaths map[string]string) error
}

// OutputResult represents the results of a simulation run for any output port
type OutputResult struct {
	PortName string
	Value    string
}

var fileAccessMutex sync.Mutex

// ReadOutputFiles reads multiple output files concurrently and returns their contents
func ReadOutputFiles(filePaths map[string]string) (map[string]string, error) {
	results := make(map[string]string)
	var wg sync.WaitGroup
	var mu sync.Mutex
	var errorFound bool
	var firstError error

	for portName, filePath := range filePaths {
		wg.Add(1)
		go func(port, path string) {
			defer wg.Done()

			content, err := ReadOutputFile(path)
			if err != nil {
				mu.Lock()
				if !errorFound {
					errorFound = true
					firstError = fmt.Errorf("failed to read output for %s: %v", port, err)
				}
				mu.Unlock()
				return
			}

			mu.Lock()
			results[port] = content
			mu.Unlock()
		}(portName, filePath)
	}

	wg.Wait()

	if errorFound {
		return nil, firstError
	}
	return results, nil
}

// CompareOutputFiles compares the contents of output files for specified ports
func CompareOutputFiles(ivDir, vlDir string, portNames []string) (map[string]bool, error) {
	results := make(map[string]bool)
	var wg sync.WaitGroup
	var mu sync.Mutex

	for _, portName := range portNames {
		wg.Add(1)
		go func(port string) {
			defer wg.Done()

			ivPath := filepath.Join(ivDir, fmt.Sprintf("iv_%s.hex", port))
			vlPath := filepath.Join(vlDir, fmt.Sprintf("vl_%s.hex", port))

			ivContent, err1 := ReadOutputFile(ivPath)
			vlContent, err2 := ReadOutputFile(vlPath)

			if err1 != nil || err2 != nil {
				return
			}

			mu.Lock()
			results[port] = (ivContent == vlContent)
			mu.Unlock()
		}(portName)
	}

	wg.Wait()
	return results, nil
}

// VerifyOutputFiles ensures output files exist and are non-empty
func VerifyOutputFiles(outputPaths map[string]string) error {
	var wg sync.WaitGroup
	var mu sync.Mutex
	var missing []string

	for portName, path := range outputPaths {
		wg.Add(1)
		go func(name, filePath string) {
			defer wg.Done()

			for retry := 0; retry < 5; retry++ {
				fileAccessMutex.Lock()
				stat, err := os.Stat(filePath)
				fileAccessMutex.Unlock()

				if err == nil && stat.Size() > 0 {
					return
				}
				time.Sleep(50 * time.Millisecond)
			}

			mu.Lock()
			missing = append(missing, name)
			mu.Unlock()
		}(portName, path)
	}

	wg.Wait()

	if len(missing) > 0 {
		return fmt.Errorf("output files not created properly for ports: %v", missing)
	}

	return nil
}

// ReadOutputFile reads the content of an output file with retries
func ReadOutputFile(path string) (string, error) {
	var content []byte
	var err error

	for retries := 0; retries < 5; retries++ {
		fileAccessMutex.Lock()
		content, err = os.ReadFile(path)
		fileAccessMutex.Unlock()

		if err == nil && len(content) > 0 {
			return strings.TrimSpace(string(content)), nil
		}
		time.Sleep(50 * time.Millisecond)
	}

	if err != nil {
		return "", fmt.Errorf("failed to read file after retries: %v", err)
	}
	return "", errors.New("file exists but is empty")
}
