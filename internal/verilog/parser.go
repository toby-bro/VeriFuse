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

func matchParameter(param string) []string {
	// Regex to capture optional type, mandatory name, and optional value.
	// Group 1: Optional type (including qualifiers like 'unsigned')
	// Group 2: Parameter name
	// Group 3: Optional default value (including the '=')
	// Group 4: Just the default value if present
	paramRegex := regexp.MustCompile(
		`^\s*(?:parameter\s+)?` + // Optional "parameter" keyword
			`(?:(logic|reg|wire|bit|int|integer|byte|shortint|longint|time|real|realtime(?:\s+(?:unsigned|signed))?)\s+)?` + // Optional Type (Group 1)
			`(\w+)` + // Parameter Name (Group 2)
			`(?:\s*(=)\s*(.+))?` + // Optional Default Value part (Group 3=equals, Group 4=value)
			`\s*(?:,|;)?$`, // Optional terminator
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
		// Use Sscanf for safer parsing
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

	// Default to a reasonable width if parsing fails or is complex
	// Return 8 as default width, but still signal an error
	return 8, fmt.Errorf(
		"could not determine width from range: %s, defaulting to 8",
		rangeStr,
	)
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

// Regular expressions for port declarations within the module body (non-ANSI style)
// These assume declarations end with a semicolon or are part of a comma-separated list.
// Adjusted to be less strict about the semicolon at the end and capture type/signedness better.
var (
	inputRegex = regexp.MustCompile(
		`^\s*input\s+(?:(logic|reg|wire|bit|int|integer|byte|shortint|longint|time|real|realtime)\s+)?(?:(signed|unsigned)\s+)?(\[\s*[\w\-\+\:\s]+\s*\])?\s*(\w+)\s*(?:,|;)?`,
	)
	outputRegex = regexp.MustCompile(
		`^\s*output\s+(?:(logic|reg|wire|bit|int|integer|byte|shortint|longint|time|real|realtime)\s+)?(?:(signed|unsigned)\s+)?(\[\s*[\w\-\+\:\s]+\s*\])?\s*(\w+)\s*(?:,|;)?`,
	)
	inoutRegex = regexp.MustCompile(
		`^\s*inout\s+(?:(logic|reg|wire|bit|int|integer|byte|shortint|longint|time|real|realtime)\s+)?(?:(signed|unsigned)\s+)?(\[\s*[\w\-\+\:\s]+\s*\])?\s*(\w+)\s*(?:,|;)?`,
	)
)

// parsePortDeclaration attempts to parse a line as a non-ANSI port declaration.
// It returns the parsed Port and true if successful, otherwise nil and false.
func parsePortDeclaration(line string) (*Port, bool) {
	var matches []string
	var direction PortDirection

	line = strings.TrimSpace(line) // Ensure leading/trailing whitespace is removed

	if m := inputRegex.FindStringSubmatch(line); len(m) > 4 {
		matches = m
		direction = INPUT
	} else if m := outputRegex.FindStringSubmatch(line); len(m) > 4 {
		matches = m
		direction = OUTPUT
	} else if m := inoutRegex.FindStringSubmatch(line); len(m) > 4 {
		matches = m
		direction = INOUT
	} else {
		return nil, false // Not a matching port declaration line
	}

	portType := strings.TrimSpace(matches[1])
	signedStr := strings.TrimSpace(matches[2])
	rangeStr := strings.TrimSpace(matches[3])
	portName := strings.TrimSpace(matches[4])

	if portType == "" {
		portType = "logic" // Default type if not specified (SystemVerilog) or wire (Verilog)
	}
	isSigned := (signedStr == "signed")
	width, err := parseRange(rangeStr)
	if err != nil {
		// If parseRange returns an error, use the returned default width (e.g., 8)
		// but still log the original error message.
		fmt.Printf(
			"Warning: Could not parse range '%s' for port '%s'. Using default width %d. Error: %v\n",
			rangeStr,
			portName,
			width, // Use the width returned by parseRange (the default)
			err,
		)
	}

	// Handle default widths for types if no range specified AND parseRange didn't error
	if width == 1 && rangeStr == "" && err == nil {
		switch portType {
		case "integer", "int", "longint", "time":
			width = 32
		case "shortint":
			width = 16
		case "byte":
			width = 8
		case "real", "realtime":
			width = 64
		}
	}

	if width == 0 { // Ensure width is at least 1 (should not happen if parseRange guarantees >= 1)
		width = 1
	}

	port := &Port{
		Name:      portName,
		Direction: direction,
		Type:      portType,
		Width:     width,
		IsSigned:  isSigned,
	}

	return port, true
}

// extractPortNamesFromListString parses the raw port list string from the module header.
// It handles ANSI style declarations within the header and creates placeholders for non-ANSI.
// Returns a map of port name to the parsed Port struct (or placeholder) and a slice maintaining the original order.
func extractPortNamesFromListString(portListStr string) (map[string]Port, []string) {
	headerPorts := make(map[string]Port)
	headerPortOrder := []string{}

	// Regex for ANSI port declarations in the header
	ansiPortRegex := regexp.MustCompile(
		`^\s*(input|output|inout)?\s*` + // Optional direction (1)
			`(logic|reg|wire|bit|int|integer|byte|shortint|longint|time|real|realtime)?\s*` + // Optional type (2)
			`(signed|unsigned)?\s*` + // Optional signedness (3)
			`(\[\s*[\w\-\+\:\s]+\s*\])?\s*` + // Optional range (4)
			`(\w+)\s*$`, // Port name (5)
	)
	// Regex for simple port names (no type/direction in header) or named connections
	simplePortRegex := regexp.MustCompile(
		`^\s*(?:\.\s*(\w+)\s*\()?\s*(\w+)\s*\)?\s*$`,
	) // Handles name and .name(name)

	for _, p := range strings.Split(portListStr, ",") {
		portDecl := strings.TrimSpace(p)
		if portDecl == "" {
			continue
		}

		portName := ""
		var port Port

		if matches := ansiPortRegex.FindStringSubmatch(portDecl); len(matches) > 5 {
			// Full ANSI declaration found
			directionStr := strings.TrimSpace(matches[1])
			portType := strings.TrimSpace(matches[2])
			signedStr := strings.TrimSpace(matches[3])
			rangeStr := strings.TrimSpace(matches[4])
			portName = strings.TrimSpace(matches[5])

			if portType == "" {
				portType = "logic" // Default type
			}
			isSigned := (signedStr == "signed")
			width, err := parseRange(rangeStr)
			if err != nil {
				// Use the default width returned by parseRange on error
				fmt.Printf(
					"Warning: Header parseRange failed for '%s' (%s): Using default width %d. Error: %v.\n",
					portName,
					rangeStr,
					width, // Use the width returned by parseRange (the default)
					err,
				)
			}

			// Determine direction
			var direction PortDirection
			switch directionStr {
			case "input":
				direction = INPUT
			case "output":
				direction = OUTPUT
			case "inout":
				direction = INOUT
			default:
				direction = INPUT
				fmt.Printf(
					"Warning: ANSI port '%s' in header missing direction. Assuming INPUT temporarily.\n",
					portName,
				)
			}

			// Handle default widths for types if no range specified AND parseRange didn't error
			if width == 1 && rangeStr == "" && err == nil {
				switch portType {
				case "integer", "int", "longint", "time":
					width = 32
				case "shortint":
					width = 16
				case "byte":
					width = 8
				case "real", "realtime":
					width = 64
				}
			}
			if width == 0 {
				width = 1
			} // Ensure minimum width

			port = Port{
				Name:      portName,
				Direction: direction,
				Type:      portType,
				Width:     width,
				IsSigned:  isSigned,
			}
		} else if matches := simplePortRegex.FindStringSubmatch(portDecl); len(matches) > 2 {
			// Simple name found (likely non-ANSI or Verilog-1995) or .name(signal)
			if matches[1] != "" { // .name(signal) case
				portName = matches[1]
			} else { // simple name case
				portName = matches[2]
			}
			// Create a placeholder, details expected in body scan
			port = Port{Name: portName, Width: 1, Type: "logic", Direction: INPUT, IsSigned: false} // Sensible defaults
		} else {
			fmt.Printf("Warning: Could not parse port declaration fragment in header: '%s'\n", portDecl)
			continue // Skip if we can't extract a name
		}

		if portName != "" {
			if _, exists := headerPorts[portName]; exists {
				fmt.Printf(
					"Warning: Duplicate port name '%s' detected in module header.\n",
					portName,
				)
			}
			headerPorts[portName] = port // Store parsed/placeholder port
			headerPortOrder = append(headerPortOrder, portName)
		}
	}

	return headerPorts, headerPortOrder
}

// scanForPortDeclarations scans the file content to find detailed port declarations (non-ANSI style).
// It returns a map of port names to fully parsed Port structs found in the body.
func scanForPortDeclarations(
	file *os.File,
	targetModule string,
) (map[string]Port, error) {
	_, err := file.Seek(0, 0) // Reset to beginning of file
	if err != nil {
		return nil, fmt.Errorf("failed to seek file: %v", err)
	}
	scanner := bufio.NewScanner(file)

	parsedPortsMap := make(map[string]Port) // Ports found in body scan

	inCommentBlock := false
	inModuleHeader := false // Track if we are between 'module ... (' and ');'
	inTargetModule := false // Track if we are inside the target module definition

	moduleStartRegex := regexp.MustCompile(
		"^\\s*module\\s+" + regexp.QuoteMeta(targetModule),
	)
	moduleEndRegex := regexp.MustCompile(`^\s*endmodule`)
	headerEndRegex := regexp.MustCompile(`\)\s*;`) // Matches the end of the port list ' );'

	for scanner.Scan() {
		line := scanner.Text()

		// Handle multi-line comments
		if strings.Contains(line, "/*") {
			if !strings.Contains(line, "*/") { // Starts but doesn't end on this line
				inCommentBlock = true
			}
			// Remove comment part if it starts and ends on the same line or just starts
			line = regexp.MustCompile(`/\*.*?\*/`).ReplaceAllString(line, "")
			line = regexp.MustCompile(`/\*.*`).ReplaceAllString(line, "")
		}
		if inCommentBlock {
			if strings.Contains(line, "*/") {
				inCommentBlock = false
				// Remove comment part if it ends on this line
				line = regexp.MustCompile(`.*\*/`).ReplaceAllString(line, "")
			} else {
				continue // Whole line is inside comment block
			}
		}
		// Handle single-line comments
		line = regexp.MustCompile(`//.*`).ReplaceAllString(line, "")
		trimmedLine := strings.TrimSpace(line) // Update trimmed line after comment removal

		if trimmedLine == "" {
			continue // Skip empty lines or lines that became empty
		}

		// Track module scope
		if !inTargetModule && moduleStartRegex.MatchString(line) {
			inTargetModule = true
			inModuleHeader = true // We are now in the header part
		}

		if !inTargetModule {
			continue // Skip lines outside the target module
		}

		if inModuleHeader && headerEndRegex.MatchString(line) {
			inModuleHeader = false // Header finished, now in body
			// Process the part of the line *before* ');' if any declaration is there
			lineBeforeHeaderEnd := headerEndRegex.Split(line, 2)[0]
			if port, ok := parsePortDeclaration(strings.TrimSpace(lineBeforeHeaderEnd)); ok {
				if _, exists := parsedPortsMap[port.Name]; !exists {
					parsedPortsMap[port.Name] = *port
				}
			}
			continue // Move to next line after header end
		}

		if moduleEndRegex.MatchString(line) {
			break // Stop scanning
		}

		// If we are inside the module body (after header, before endmodule)
		if !inModuleHeader && inTargetModule {
			// Attempt to parse the line as a non-ANSI port declaration
			if port, ok := parsePortDeclaration(trimmedLine); ok {
				// Store the details found in the body, avoid overwriting if already found (first declaration wins)
				if _, exists := parsedPortsMap[port.Name]; !exists {
					parsedPortsMap[port.Name] = *port
				}
			}
		}
	}

	if err := scanner.Err(); err != nil {
		return nil, fmt.Errorf("error scanning file: %v", err)
	}

	return parsedPortsMap, nil
}

// applyPortDeclarationFallback adds ports based on naming conventions if detailed declarations were missing.
// This now acts on ports that were in the header list but had no corresponding body declaration (if they were placeholders).
func applyPortDeclarationFallback(
	module *Module,
	headerPorts map[string]Port,
	parsedPortsMap map[string]Port,
) {
	portsToAdd := []Port{}
	existingPorts := make(map[string]bool)
	for _, p := range module.Ports {
		existingPorts[p.Name] = true
	}

	for name, headerPort := range headerPorts {
		_, definedInBody := parsedPortsMap[name]
		_, alreadyAdded := existingPorts[name]

		// Check if it was a placeholder (minimal info) and wasn't defined in body or already added
		isPlaceholder := headerPort.Width == 1 && headerPort.Type == "logic" &&
			headerPort.Direction == INPUT &&
			!headerPort.IsSigned

		if isPlaceholder && !definedInBody && !alreadyAdded {
			fmt.Printf(
				"Warning: Port '%s' listed in header but not defined in body. Applying fallback naming convention.\n",
				name,
			)
			// Apply naming convention fallback
			var direction PortDirection
			switch {
			case strings.HasSuffix(name, "_i") || strings.HasSuffix(name, "_in"):
				direction = INPUT
			case strings.HasSuffix(name, "_o") || strings.HasSuffix(name, "_out"):
				direction = OUTPUT
			default:
				direction = INPUT // Default to input
			}
			fallbackPort := Port{
				Name:      name,
				Direction: direction,
				Type:      "logic", // Default type
				Width:     1,       // Default to scalar
				IsSigned:  false,
			}
			portsToAdd = append(portsToAdd, fallbackPort)
			existingPorts[name] = true // Mark as added
		}
	}
	module.Ports = append(module.Ports, portsToAdd...)
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
		// Try finding *any* module if the target wasn't found explicitly
		generalMatches := matchGeneralModule(content)
		if len(generalMatches) < 4 {
			return nil, fmt.Errorf(
				"no module found matching '%s' or any other name in the file: %w",
				targetModule,
				err,
			)
		}
		fmt.Printf(
			"Warning: Target module '%s' not found, parsing first module '%s' instead.\n",
			targetModule,
			string(generalMatches[1]),
		)
		actualTargetModule = string(generalMatches[1])
		if len(generalMatches[2]) > 0 { // Parameters exist
			paramListStr = string(generalMatches[2])
			portListStr = string(generalMatches[3])
		} else { // No parameters
			portListStr = string(generalMatches[3])
		}
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
		parseParameters(paramListStr, module)
	}

	// --- Enhanced Port Parsing ---
	// 1. Parse the header list (ANSI or simple names)
	headerPorts, headerPortOrder := extractPortNamesFromListString(portListStr)

	// 2. Scan the module body for detailed non-ANSI declarations
	parsedPortsMap, err := scanForPortDeclarations(file, actualTargetModule)
	if err != nil {
		return nil, fmt.Errorf("error scanning for port declarations: %v", err)
	}

	// 3. Build the final Ports slice based on header order, combining header and body info
	processedPorts := make(
		map[string]bool,
	) // Track ports added to avoid duplicates if logic overlaps
	for _, nameInHeader := range headerPortOrder {
		if processedPorts[nameInHeader] {
			continue // Already processed (e.g., duplicate name in header)
		}

		headerPort := headerPorts[nameInHeader]               // Get the port info parsed from header (ANSI or placeholder)
		bodyPort, foundInBody := parsedPortsMap[nameInHeader] // Get info found in body (non-ANSI)

		finalPort := headerPort // Start with header info

		// Determine if the header port was just a placeholder (simple name)

		if foundInBody {
			// If found in body, these details are more specific/correct for non-ANSI ports
			// or override potentially incomplete ANSI header info.
			finalPort.Direction = bodyPort.Direction
			finalPort.Type = bodyPort.Type
			finalPort.Width = bodyPort.Width
			finalPort.IsSigned = bodyPort.IsSigned
		}

		// Final check for width=0 (shouldn't happen with parseRange defaulting to 1 on error)
		if finalPort.Width == 0 {
			fmt.Printf("Warning: Port '%s' ended up with width 0. Setting to 1.\n", finalPort.Name)
			finalPort.Width = 1
		}

		module.Ports = append(module.Ports, finalPort)
		processedPorts[nameInHeader] = true
	}

	// 4. Apply fallback logic for any ports found in the list but not fully defined
	applyPortDeclarationFallback(module, headerPorts, parsedPortsMap)

	if len(module.Ports) == 0 && portListStr != "" {
		// If portListStr was not empty but we still have no ports, something went wrong
		return nil, fmt.Errorf(
			"failed to parse any ports for module %s despite port list being present",
			actualTargetModule,
		)
	} else if len(module.Ports) == 0 {
		// If portListStr was empty and we found nothing, it might be a module with no ports
		fmt.Printf("Warning: No ports found or parsed for module %s. Module might have no ports.\n", actualTargetModule)
	}

	return module, nil
}

// parseParameters extracts parameters from the module parameter list
func parseParameters(paramList string, module *Module) {
	// Split by commas, but handle multi-line parameters carefully
	// A simple split might break if a value contains a comma (e.g., in string literal)
	// For now, assume simple comma separation works for typical parameter lists.
	// TODO: Improve splitting logic if needed for complex parameter values.
	params := strings.Split(paramList, ",")

	for _, param := range params {
		param = strings.TrimSpace(param)
		if param == "" {
			continue
		}

		// Use helper function to match parameter
		matches := matchParameter(param)

		// Expected matches:
		// matches[0]: Full match
		// matches[1]: Type (optional)
		// matches[2]: Name
		// matches[3]: Equals sign (if value exists)
		// matches[4]: Value (if value exists)

		if len(matches) >= 3 { // Need at least the name (Group 2)
			paramType := strings.TrimSpace(matches[1]) // Type is in Group 1
			paramName := strings.TrimSpace(matches[2]) // Name is in Group 2
			paramValue := ""
			if len(matches) >= 5 && matches[3] == "=" { // Check if Group 3 captured '='
				paramValue = strings.TrimSpace(matches[4]) // Value is in Group 4
			}

			// Ensure paramType is not accidentally set to "parameter" if keyword was matched but no type specified
			// The regex structure prevents this now, but double-check. Group 1 should be empty if no type keyword found.

			module.Parameters = append(module.Parameters, Parameter{
				Name:         paramName,
				Type:         paramType, // Will be "" if no type keyword was found
				DefaultValue: paramValue,
			})
		} else {
			fmt.Printf("Warning: Could not parse parameter fragment: '%s'\n", param)
		}
	}
}
