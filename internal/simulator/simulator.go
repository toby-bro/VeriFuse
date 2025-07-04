package simulator

import (
	"context"
	"errors"
	"fmt"
	"os"
	"strings"
	"sync"
	"time"

	"github.com/toby-bro/pfuzz/pkg/utils"
	"github.com/toby-bro/pfuzz/pkg/verilog"
)

type Type int

const (
	VERILATOR Type = iota
	IVERILOG
	CXXRTL
	CXXSLG
	QUARTUS
	XCELLIUM
	VCS
	MODELSIM
)

func (t Type) String() string {
	switch t {
	case VERILATOR:
		return "Verilator"
	case IVERILOG:
		return "Iverilog"
	case CXXRTL:
		return "CXXRTL"
	case CXXSLG:
		return "CXXSLG"
	case QUARTUS:
		return "Quartus"
	case XCELLIUM:
		return "Xcilium"
	case VCS:
		return "VCS"
	case MODELSIM:
		return "Modelsim"
	default:
		return "Unknown Simulator"
	}
}

// Simulator defines the interface for RTL simulators
type Simulator interface {
	// Compile compiles the simulator from source files with context for timeout
	Compile(ctx context.Context) error

	// RunTest runs the simulator with the provided input and output files
	// inputDir is the directory containing input files
	// outputPaths maps port names to output file paths
	RunTest(ctx context.Context, inputDir string, outputPaths map[*verilog.Port]string) error
	FailedCuzUnsupportedFeature(log error) (bool, error)
}

// OutputResult represents the results of a simulation run for any output port
type OutputResult struct {
	PortName string
	Value    string
}

var fileAccessMutex sync.Mutex

// ReadOutputFiles reads multiple output files concurrently and returns their contents
func ReadOutputFiles(filePaths map[*verilog.Port]string) (map[*verilog.Port]string, error) {
	results := make(map[*verilog.Port]string)
	var wg sync.WaitGroup
	var mu sync.Mutex
	var errorFound bool
	var firstError error

	for port, filePath := range filePaths {
		wg.Add(1)
		go func(port *verilog.Port, path string) {
			defer wg.Done()

			content, err := ReadOutputFile(path)
			if err != nil {
				mu.Lock()
				if !errorFound {
					errorFound = true
					firstError = fmt.Errorf("failed to read output for %s: %v", port.Name, err)
				}
				mu.Unlock()
				return
			}

			mu.Lock()
			results[port] = content
			mu.Unlock()
		}(port, filePath)
	}

	wg.Wait()

	if errorFound {
		return nil, firstError
	}
	return results, nil
}

// VerifyOutputFiles ensures output files exist and are non-empty
func VerifyOutputFiles(outputPaths map[*verilog.Port]string) error {
	var wg sync.WaitGroup
	var mu sync.Mutex
	var missing []*verilog.Port

	for port, path := range outputPaths {
		wg.Add(1)
		go func(port *verilog.Port, filePath string) {
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
			missing = append(missing, port)
			mu.Unlock()
		}(port, path)
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

func TestAvailableSimulators(debugger *utils.DebugLogger) []Type {
	availableSimulators := []Type{}

	if err := TestIVerilogTool(); err != nil {
		debugger.Warn("iverilog tool check failed: %v", err)
	} else {
		debugger.Debug("IVerilog tool found.")
		availableSimulators = append(availableSimulators, IVERILOG)
	}
	if err := TestVerilatorTool(); err != nil {
		debugger.Warn("verilator tool check failed: %v", err)
	} else {
		debugger.Debug("Verilator tool found.")
		availableSimulators = append(availableSimulators, VERILATOR)
	}
	if err := TestCXXRTLTool(false); err != nil {
		debugger.Warn("cxxrtl tool check failed: %v", err)
	} else {
		debugger.Debug("CXXRTL tool found.")
		availableSimulators = append(availableSimulators, CXXRTL)
		if err := TestCXXRTLTool(true); err != nil {
			debugger.Warn("cxxrtl tool check failed: %v", err)
		} else {
			debugger.Debug("Slang found.")
			availableSimulators = append(availableSimulators, CXXSLG)
		}
	}
	return availableSimulators
}
