package verilog

import (
	"bufio"
	"errors"
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

// Parameter represents a module parameter
type Parameter struct {
	Name         string
	Type         string
	DefaultValue string
}

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
	Name       string
	Filename   string
	Ports      []Port
	Parameters []Parameter
	Content    string
}

// --- Regex Helper Functions ---

func matchSpecificModule(content []byte, targetModule string) [][]byte {
	// Find module declaration - supports parameter section with #(...)
	moduleRegex := regexp.MustCompile(
		fmt.Sprintf(
			`module\s+%s\s*(?:#\s*\(([\s\S]*?)\))?\s*\(([\s\S]*?)\);`,
			regexp.QuoteMeta(targetModule),
		),
	)
	return moduleRegex.FindSubmatch(content)
}

func matchGeneralModule(content []byte) [][]byte {
	// Try with any module name if specific module not found
	generalModuleRegex := regexp.MustCompile(
		`module\s+(\w+)\s*(?:#\s*\(([\s\S]*?)\))?\s*\(([\s\S]*?)\);`,
	)
	return generalModuleRegex.FindSubmatch(content)
}

func extractPortNameFromList(portString string) string {
	portName := strings.TrimSpace(portString)
	// Extract just the identifier part without any data type or direction
	if matches := regexp.MustCompile(`\.(\w+)\s*\(`).FindStringSubmatch(portName); len(
		matches,
	) > 1 {
		// Named port connection like .clk(clk)
		return matches[1]
	} else if matches := regexp.MustCompile(`(\w+)\s*$`).FindStringSubmatch(portName); len(matches) > 1 {
		// Simple port like 'clk' or at the end of a declaration like 'input clk'
		return matches[1]
	}
	return "" // Return empty if no valid name found
}

func matchInputPort(line string) []string {
	inputRegex := regexp.MustCompile(
		`input\s+(reg|wire|logic)?\s*(\[\s*[\w\-\+\:]+\s*\])?\s*(\w+)\s*`,
	)
	return inputRegex.FindStringSubmatch(line)
}

func matchOutputPort(line string) []string {
	outputRegex := regexp.MustCompile(
		`output\s+(reg|wire|logic)?\s*(\[\s*[\w\-\+\:]+\s*\])?\s*(\w+)\s*`,
	)
	return outputRegex.FindStringSubmatch(line)
}

func matchInoutPort(line string) []string {
	inoutRegex := regexp.MustCompile(
		`inout\s+(reg|wire|logic)?\s*(\[\s*[\w\-\+\:]+\s*\])?\s*(\w+)\s*`,
	)
	return inoutRegex.FindStringSubmatch(line)
}

func matchParameter(param string) []string {
	// Better parameter regex that handles both formats:
	// 1. parameter [type] NAME = VALUE
	// 2. parameter type qualifier NAME = VALUE (e.g., int unsigned NUM_REQS = 2)
	paramRegex := regexp.MustCompile(
		`(?:parameter)?\s*(?:(\w+(?:\s+(?:unsigned|signed))?)|(\w+))\s+(\w+)(?:\s*=\s*([^,]+))?`,
	)
	return paramRegex.FindStringSubmatch(param)
}

// --- End Regex Helper Functions ---

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
		n, err := fmt.Sscanf(matches[1], "%d", &width)
		if err != nil || n != 1 {
			return 0, fmt.Errorf("invalid range format: %s", rangeStr)
		}
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
	lowerRangeStr := strings.ToLower(rangeStr)
	switch {
	case strings.Contains(lowerRangeStr, "addr"):
		return 32, nil // Address typically 32 bits
	case strings.Contains(lowerRangeStr, "data"):
		return 32, nil // Data typically 32 bits
	case strings.Contains(lowerRangeStr, "byte"):
		return 8, nil // Byte is 8 bits
	case strings.Contains(lowerRangeStr, "word"):
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

	// Use helper function to find module declaration
	moduleMatches := matchSpecificModule(content, targetModule)

	if len(moduleMatches) < 3 {
		// Use helper function to find general module declaration
		generalMatches := matchGeneralModule(content)

		if len(generalMatches) < 4 {
			return nil, errors.New("no module found in the file")
		}

		targetModule = string(generalMatches[1])
		// Reconstruct moduleMatches structure for consistent handling below
		var paramListBytes, portListBytes []byte
		if len(generalMatches[2]) > 0 { // Parameters exist
			paramListBytes = generalMatches[2]
			portListBytes = generalMatches[3]
		} else { // No parameters
			portListBytes = generalMatches[3] // Port list is the 3rd group (index 2 is empty)
		}
		moduleMatches = [][]byte{generalMatches[0], paramListBytes, portListBytes}
	}

	// Extract parameters and port list
	var paramList string
	var portList string

	if len(moduleMatches) >= 3 {
		if len(moduleMatches[1]) > 0 {
			paramList = string(moduleMatches[1])
		}
		portList = string(moduleMatches[2])
	}

	// Create a new module structure
	module := &Module{
		Name:       targetModule,
		Filename:   filename,
		Ports:      []Port{},
		Parameters: []Parameter{},
		Content:    string(content),
	}

	// Parse parameters if they exist
	if paramList != "" {
		parseParameters(paramList, module)
	}

	// Extract module port names from the port list using helper function
	portNames := make(map[string]bool)
	for _, p := range strings.Split(portList, ",") {
		portName := extractPortNameFromList(p)
		if portName != "" {
			portNames[portName] = true
		}
	}

	// Now scan the file to find port declarations
	_, err = file.Seek(0, 0) // Reset to beginning of file
	if err != nil {
		return nil, fmt.Errorf("failed to seek file: %v", err)
	}
	scanner := bufio.NewScanner(file)

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
			break // Exit loop once endmodule is found
		}

		if !inModule {
			continue
		}

		// Use helper functions to check for port declarations
		if matches := matchInputPort(line); len(matches) > 3 {
			isReg := matches[1] == "reg"
			rangeStr := matches[2]
			portName := strings.TrimSpace(matches[3]) // Clean port name

			if portNames[portName] {
				width, _ := parseRange(rangeStr)
				module.Ports = append(module.Ports, Port{
					Name:      portName,
					Direction: INPUT,
					Width:     width,
					IsSigned:  false,
					IsReg:     isReg,
				})
			}
		} else if matches := matchOutputPort(line); len(matches) > 3 {
			isReg := matches[1] == "reg"
			rangeStr := matches[2]
			portName := strings.TrimSpace(matches[3]) // Clean port name

			if portNames[portName] {
				width, _ := parseRange(rangeStr)
				module.Ports = append(module.Ports, Port{
					Name:      portName,
					Direction: OUTPUT,
					Width:     width,
					IsSigned:  false,
					IsReg:     isReg,
				})
			}
		} else if matches := matchInoutPort(line); len(matches) > 3 {
			isReg := matches[1] == "reg"
			rangeStr := matches[2]
			portName := strings.TrimSpace(matches[3]) // Clean port name

			if portNames[portName] {
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
	}

	// Fall back to simpler port list extraction if we couldn't find port declarations
	if len(module.Ports) == 0 && len(portNames) > 0 { // Check if portNames were extracted
		// Basic heuristic: assume inputs end with _i, outputs with _o
		for portName := range portNames {
			var direction PortDirection
			switch {
			case strings.HasSuffix(portName, "_i") || strings.HasSuffix(portName, "_in"):
				direction = INPUT
			case strings.HasSuffix(portName, "_o") || strings.HasSuffix(portName, "_out"):
				direction = OUTPUT
			default:
				// Default to input if no suffix matches
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

// parseParameters extracts parameters from the module parameter list
func parseParameters(paramList string, module *Module) {
	// Split by commas, but handle multi-line parameters
	params := strings.Split(paramList, ",")

	for _, param := range params {
		param = strings.TrimSpace(param)
		if param == "" {
			continue
		}

		// Use helper function to match parameter
		matches := matchParameter(param)

		if len(matches) >= 4 {
			var paramType, paramName, paramValue string

			// Extract type and name based on which pattern matched
			if matches[1] != "" {
				// Case with type qualifier like "int unsigned"
				paramType = strings.TrimSpace(matches[1])
				paramName = strings.TrimSpace(matches[3])
			} else {
				// Simple case like "parameter bit NAME"
				paramType = strings.TrimSpace(matches[2])
				paramName = strings.TrimSpace(matches[3])
			}

			// Get default value if present
			if len(matches) >= 5 && matches[4] != "" {
				paramValue = strings.TrimSpace(matches[4])
			}

			module.Parameters = append(module.Parameters, Parameter{
				Name:         paramName,
				Type:         paramType,
				DefaultValue: paramValue,
			})
		}
	}
}
