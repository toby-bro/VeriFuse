package verilog

import (
	"bufio"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"regexp"
	"strings"
)

// PortDirection represents the direction of a module port
type PortDirection int

const (
	INPUT PortDirection = iota
	OUTPUT
	INOUT
)

// Port represents a single port in a Verilog module
type Port struct {
	Name      string
	Direction PortDirection
	Width     int  // Width in bits (1 for scalar)
	IsSigned  bool // Whether the port is signed
	IsReg     bool // Whether the port is reg type
}

// Module represents a parsed Verilog module
type Module struct {
	Name     string
	Filename string
	Ports    []Port
	Content  string
}

// Utility functions for bit width parsing
func parseRange(rangeStr string) (int, error) {
	// Handle common formats: [7:0], [WIDTH-1:0], etc.
	rangeStr = strings.TrimSpace(rangeStr)

	if rangeStr == "" {
		return 1, nil // No range means scalar (1-bit)
	}

	// Simple case [N:0]
	simpleRangeRegex := regexp.MustCompile(`\[\s*(\d+)\s*:\s*0\s*\]`)
	if matches := simpleRangeRegex.FindStringSubmatch(rangeStr); len(matches) > 1 {
		var width int
		fmt.Sscanf(matches[1], "%d", &width)
		return width + 1, nil
	}

	// Add special handling for [31:0] which might be appearing in various formats
	if strings.Contains(rangeStr, "31:0") || strings.Contains(rangeStr, "32-1:0") {
		return 32, nil
	}

	// Check for explicit width indicators in the port name or range
	if strings.Contains(strings.ToLower(rangeStr), "32") ||
		strings.Contains(strings.ToLower(rangeStr), "word") {
		return 32, nil
	}

	// Handle more complex expressions by approximation
	if strings.Contains(strings.ToLower(rangeStr), "addr") {
		return 32, nil // Address typically 32 bits
	} else if strings.Contains(strings.ToLower(rangeStr), "data") {
		return 32, nil // Data typically 32 bits
	} else if strings.Contains(strings.ToLower(rangeStr), "byte") {
		return 8, nil // Byte is 8 bits
	} else if strings.Contains(strings.ToLower(rangeStr), "word") {
		return 32, nil // Word typically 32 bits
	}

	// Default to a reasonable width
	return 8, nil
}

// ParseVerilogFile parses a Verilog file and extracts module information
func ParseVerilogFile(filename string, targetModule string) (*Module, error) {
	file, err := os.Open(filename)
	if err != nil {
		return nil, fmt.Errorf("failed to open file: %v", err)
	}
	defer file.Close()

	content, err := io.ReadAll(file)
	if err != nil {
		return nil, fmt.Errorf("failed to read file: %v", err)
	}

	// If no specific module name is provided, derive it from the filename
	if targetModule == "" {
		baseName := filepath.Base(filename)
		targetModule = strings.TrimSuffix(baseName, filepath.Ext(baseName))
	}

	// Find module declaration
	moduleRegex := regexp.MustCompile(fmt.Sprintf(`module\s+%s\s*\(([\s\S]*?)\);`, regexp.QuoteMeta(targetModule)))
	moduleMatches := moduleRegex.FindSubmatch(content)

	if len(moduleMatches) < 2 {
		// Try with any module name if specific module not found
		generalModuleRegex := regexp.MustCompile(`module\s+(\w+)\s*\(([\s\S]*?)\);`)
		generalMatches := generalModuleRegex.FindSubmatch(content)

		if len(generalMatches) < 3 {
			return nil, fmt.Errorf("no module found in the file")
		}

		targetModule = string(generalMatches[1])
		moduleMatches = [][]byte{generalMatches[0], generalMatches[2]}
	}

	portList := string(moduleMatches[1])

	// Create a new module structure
	module := &Module{
		Name:     targetModule,
		Filename: filename,
		Ports:    []Port{},
		Content:  string(content),
	}

	// Now scan the file to find port declarations
	file.Seek(0, 0) // Reset to beginning of file
	scanner := bufio.NewScanner(file)

	// Regular expressions for port declarations - updated to better isolate port names
	inputRegex := regexp.MustCompile(`input\s+(reg|wire|logic)?\s*(\[\s*[\w\-\+\:]+\s*\])?\s*(\w+)\s*`)   //(?:[,;]|\s*\)\s*;)`)
	outputRegex := regexp.MustCompile(`output\s+(reg|wire|logic)?\s*(\[\s*[\w\-\+\:]+\s*\])?\s*(\w+)\s*`) //(?:[,;]|\s*\)\s*;)`)
	inoutRegex := regexp.MustCompile(`inout\s+(reg|wire|logic)?\s*(\[\s*[\w\-\+\:]+\s*\])?\s*(\w+)\s*`)   //(?:[,;]|\s*\)\s*;)`)

	// Clean declaration regex to extract just the port name from a full declaration line
	cleanNameRegex := regexp.MustCompile(`.*\s+(\w+)\s*$`)

	// Process each line
	inComment := false
	inModule := false

	for scanner.Scan() {
		line := scanner.Text()

		// Skip comments
		if strings.Contains(line, "/*") {
			inComment = true
		}
		if inComment {
			if strings.Contains(line, "*/") {
				inComment = false
			}
			continue
		}
		if strings.HasPrefix(strings.TrimSpace(line), "//") {
			continue
		}

		// Track if we're inside the target module declaration
		if strings.Contains(line, "module "+targetModule) {
			inModule = true
		} else if strings.Contains(line, "endmodule") && inModule {
			inModule = false
			break
		}

		if !inModule {
			continue
		}

		// Check for input ports
		if matches := inputRegex.FindStringSubmatch(line); len(matches) > 3 {
			isReg := matches[1] == "reg"
			rangeStr := matches[2]
			portName := matches[3]

			// Clean any comments or extra whitespace from portName
			portName = strings.TrimSpace(portName)

			width, _ := parseRange(rangeStr)

			module.Ports = append(module.Ports, Port{
				Name:      portName,
				Direction: INPUT,
				Width:     width,
				IsSigned:  false, // Assume unsigned by default
				IsReg:     isReg,
			})
		}

		// Check for output ports
		if matches := outputRegex.FindStringSubmatch(line); len(matches) > 3 {
			isReg := matches[1] == "reg"
			rangeStr := matches[2]
			portName := matches[3]

			// Clean any comments or extra whitespace from portName
			portName = strings.TrimSpace(portName)

			width, _ := parseRange(rangeStr)

			module.Ports = append(module.Ports, Port{
				Name:      portName,
				Direction: OUTPUT,
				Width:     width,
				IsSigned:  false, // Assume unsigned by default
				IsReg:     isReg,
			})
		}

		// Check for inout ports
		if matches := inoutRegex.FindStringSubmatch(line); len(matches) > 3 {
			isReg := matches[1] == "reg"
			rangeStr := matches[2]
			portName := matches[3]

			// Clean any comments or extra whitespace from portName
			portName = strings.TrimSpace(portName)

			width, _ := parseRange(rangeStr)

			module.Ports = append(module.Ports, Port{
				Name:      portName,
				Direction: INOUT,
				Width:     width,
				IsSigned:  false,
				IsReg:     isReg,
			})
		}
	}

	// If we couldn't find port declarations, try to extract from port list
	if len(module.Ports) == 0 {
		// Extract port names from portList
		portNames := []string{}
		for _, p := range strings.Split(portList, ",") {
			portName := strings.TrimSpace(p)

			// Extract just the identifier part if it's a full declaration
			if matches := cleanNameRegex.FindStringSubmatch(portName); len(matches) > 1 {
				portName = matches[1]
			}

			if portName != "" {
				portNames = append(portNames, portName)
			}
		}

		// Basic heuristic: assume inputs end with _i, outputs with _o
		for _, portName := range portNames {
			var direction PortDirection
			if strings.HasSuffix(portName, "_i") || strings.HasSuffix(portName, "_in") {
				direction = INPUT
			} else if strings.HasSuffix(portName, "_o") || strings.HasSuffix(portName, "_out") {
				direction = OUTPUT
			} else {
				// Default to input
				direction = INPUT
			}

			module.Ports = append(module.Ports, Port{
				Name:      portName,
				Direction: direction,
				Width:     1, // Default to scalar
				IsSigned:  false,
				IsReg:     false,
			})
		}
	}

	if len(module.Ports) == 0 {
		return nil, fmt.Errorf("no ports found for module %s", targetModule)
	}

	return module, nil
}
