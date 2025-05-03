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
	Type      string // e.g., logic, reg, wire, int, bit
	Width     int    // Width in bits (1 for scalar)
	IsSigned  bool   // Whether the port is signed
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

// openAndReadFile opens and reads the entire content of the specified file.
func openAndReadFile(filename string) (*os.File, []byte, error) {
	file, err := os.Open(filename)
	if err != nil {
		return nil, nil, fmt.Errorf("failed to open file: %v", err)
	}
	// Note: The caller is responsible for closing the file.

	content, err := io.ReadAll(file)
	if err != nil {
		file.Close() // Close file on read error
		return nil, nil, fmt.Errorf("failed to read file: %v", err)
	}
	return file, content, nil
}

// determineTargetModule derives the target module name from the filename if not provided.
func determineTargetModule(filename string, providedTargetModule string) string {
	if providedTargetModule == "" {
		baseName := filepath.Base(filename)
		return strings.TrimSuffix(baseName, filepath.Ext(baseName))
	}
	return providedTargetModule
}

// findModuleDeclaration searches the content for the module definition and extracts parameter/port lists.
func findModuleDeclaration(content []byte, targetModule string) (string, string, string, error) {
	moduleMatches := matchSpecificModule(content, targetModule)
	actualTargetModule := targetModule

	if len(moduleMatches) < 3 {
		generalMatches := matchGeneralModule(content)
		if len(generalMatches) < 4 {
			return "", "", "", errors.New("no module found in the file")
		}

		actualTargetModule = string(generalMatches[1])
		var paramListBytes, portListBytes []byte
		if len(generalMatches[2]) > 0 { // Parameters exist
			paramListBytes = generalMatches[2]
			portListBytes = generalMatches[3]
		} else { // No parameters
			portListBytes = generalMatches[3]
		}
		moduleMatches = [][]byte{generalMatches[0], paramListBytes, portListBytes}
	}

	var paramListStr, portListStr string
	if len(moduleMatches) >= 3 {
		if len(moduleMatches[1]) > 0 {
			paramListStr = string(moduleMatches[1])
		}
		portListStr = string(moduleMatches[2])
	}

	return actualTargetModule, paramListStr, portListStr, nil
}

// extractPortNamesFromListString parses the raw port list string and returns a map of port names.
func extractPortNamesFromListString(portListStr string) map[string]bool {
	portNames := make(map[string]bool)
	for _, p := range strings.Split(portListStr, ",") {
		portName := extractPortNameFromList(p) // Uses existing regex helper
		if portName != "" {
			portNames[portName] = true
		}
	}
	return portNames
}

// scanForPortDeclarations scans the file content to find detailed port declarations.
func scanForPortDeclarations(
	file *os.File,
	targetModule string,
	portNames map[string]bool,
	module *Module,
) error {
	_, err := file.Seek(0, 0) // Reset to beginning of file
	if err != nil {
		return fmt.Errorf("failed to seek file: %v", err)
	}
	scanner := bufio.NewScanner(file)

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

		// Check for input ports
		if matches := matchInputPort(line); len(matches) > 3 {
			portType := strings.TrimSpace(matches[1])
			if portType == "" {
				portType = "logic" // Default type if not specified
			}
			rangeStr := matches[2]
			portName := strings.TrimSpace(matches[3])

			if portNames[portName] {
				width, _ := parseRange(rangeStr)
				module.Ports = append(module.Ports, Port{
					Name:      portName,
					Direction: INPUT,
					Type:      portType,
					Width:     width,
					IsSigned:  false, // Assume unsigned by default
				})
			}
		}

		// Check for output ports
		if matches := matchOutputPort(line); len(matches) > 3 {
			portType := strings.TrimSpace(matches[1])
			if portType == "" {
				portType = "logic" // Default type if not specified
			}
			rangeStr := matches[2]
			portName := strings.TrimSpace(matches[3])

			if portNames[portName] {
				width, _ := parseRange(rangeStr)
				module.Ports = append(module.Ports, Port{
					Name:      portName,
					Direction: OUTPUT,
					Type:      portType,
					Width:     width,
					IsSigned:  false, // Assume unsigned by default
				})
			}
		}

		// Check for inout ports
		if matches := matchInoutPort(line); len(matches) > 3 {
			portType := strings.TrimSpace(matches[1])
			if portType == "" {
				portType = "logic" // Default type if not specified
			}
			rangeStr := matches[2]
			portName := strings.TrimSpace(matches[3])

			if portNames[portName] {
				width, _ := parseRange(rangeStr)
				module.Ports = append(module.Ports, Port{
					Name:      portName,
					Direction: INOUT,
					Type:      portType,
					Width:     width,
					IsSigned:  false,
				})
				delete(portNames, portName) // Remove found port
			}
		}
	}
	return scanner.Err()
}

// applyPortDeclarationFallback adds ports based on naming conventions if detailed declarations were missing.
func applyPortDeclarationFallback(remainingPortNames map[string]bool, module *Module) {
	if len(module.Ports) == 0 && len(remainingPortNames) > 0 {
		for portName := range remainingPortNames {
			var direction PortDirection
			switch {
			case strings.HasSuffix(portName, "_i") || strings.HasSuffix(portName, "_in"):
				direction = INPUT
			case strings.HasSuffix(portName, "_o") || strings.HasSuffix(portName, "_out"):
				direction = OUTPUT
			default:
				direction = INPUT // Default to input
			}
			module.Ports = append(module.Ports, Port{
				Name:      portName,
				Direction: direction,
				Type:      "logic", // Default type
				Width:     1,       // Default to scalar
				IsSigned:  false,
			})
		}
	}
}

// ParseVerilogFile parses a Verilog file and extracts module information
func ParseVerilogFile(filename string, providedTargetModule string) (*Module, error) {
	file, content, err := openAndReadFile(filename)
	if err != nil {
		return nil, err
	}
	defer file.Close()

	targetModule := determineTargetModule(filename, providedTargetModule)

	actualTargetModule, paramListStr, portListStr, err := findModuleDeclaration(
		content,
		targetModule,
	)
	if err != nil {
		return nil, err
	}

	module := &Module{
		Name:       actualTargetModule,
		Filename:   filename,
		Ports:      []Port{},
		Parameters: []Parameter{},
		Content:    string(content),
	}

	// Parse parameters if they exist
	if paramListStr != "" {
		parseParameters(paramListStr, module) // Assumes parseParameters is okay as is
	}

	// Extract port names from the list in the module definition
	portNamesMap := extractPortNamesFromListString(portListStr)

	// Scan the file content for detailed port declarations (input/output/inout)
	if err := scanForPortDeclarations(file, actualTargetModule, portNamesMap, module); err != nil {
		return nil, fmt.Errorf("error scanning for port declarations: %v", err)
	}

	// Apply fallback logic for any ports found in the list but not in declarations
	applyPortDeclarationFallback(portNamesMap, module)

	if len(module.Ports) == 0 {
		return nil, fmt.Errorf("no ports found for module %s", actualTargetModule)
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
