package verilog

import (
	"bufio"
	"bytes"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"

	"github.com/toby-bro/pfuzz/pkg/utils"
)

// PortDirection represents the direction of a module port
type (
	PortDirection int
	PortType      int
)

const (
	INPUT PortDirection = iota
	OUTPUT
	INOUT
	INTERNAL
)

const (
	REG PortType = iota
	WIRE
	INTEGER
	REAL
	TIME
	REALTIME
	LOGIC // SystemVerilog from now
	BIT
	BYTE
	SHORTINT
	INT
	LONGINT
	SHORTREAL
	STRING // sort of reg but you know...
	STRUCT
	VOID
	ENUM
	USERDEFINED
	UNKNOWN
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
	Type      PortType // e.g., logic, reg, wire, int, bit
	Width     int      // Width in bits (1 for scalar)
	IsSigned  bool     // Whether the port is signed
}

// Module represents a parsed Verilog module
type Module struct {
	Name       string
	Ports      []Port
	Parameters []Parameter
	Body       string
}

type Variable struct {
	Name         string
	Type         PortType
	Width        int
	Unsigned     bool
	Array        []int
	ParentStruct *Struct
	ParentClass  *Class
}

type Struct struct {
	Name      string
	Variables []*Variable
}

// We do NOT support virtual classes and static functions yet
// TODO: #4 Add support for virtual classes and static functionsto get parametrized tasks https://stackoverflow.com/questions/57755991/passing-parameters-to-a-verilog-function
type Function struct {
	Name  string
	Ports []Port
	Body  string
}

type Task struct {
	Name  string
	Ports []Port
	Body  string
}

type Class struct {
	Name       string
	Parameters []Parameter
	Body       string
	Tasks      []Task
	Functions  []Function
	isVirtual  bool
	extends    string
}

type ModPort struct {
	Name    string
	Inputs  []string
	Outputs []string
}

type Interface struct {
	Name       string
	Variables  []Variable
	ModPorts   []ModPort
	Parameters []Parameter
	Body       string
}

type VerilogFile struct { // nolint:revive
	Name          string
	Modules       map[string]*Module
	Interfaces    map[string]*Interface
	Classes       map[string]*Class
	Structs       map[string]*Struct
	DependancyMap map[string]*DependencyNode
}

type DependencyNode struct {
	Name      string
	DependsOn []string
}

// TODO: #5 Improve the type for structs, enums, userdefined types...
func GetPortType(portTypeString string) PortType {
	switch strings.ToLower(portTypeString) {
	case "reg":
		return REG
	case "wire":
		return WIRE
	case "integer":
		return INTEGER
	case "real":
		return REAL
	case "time":
		return TIME
	case "realtime":
		return REALTIME
	case "logic":
		return LOGIC
	case "bit":
		return BIT
	case "byte":
		return BYTE
	case "shortint":
		return SHORTINT
	case "int":
		return INT
	case "longint":
		return LONGINT
	case "shortreal":
		return SHORTREAL
	case "string":
		return STRING
	case "struct":
		return STRUCT
	case "void":
		return VOID
	case "enum":
		return ENUM
	default:
		return UNKNOWN
	}
}

func GetWidthForType(portType PortType) int {
	switch portType { //nolint:exhaustive
	case REG, WIRE, LOGIC, BIT:
		return 1
	case INTEGER, INT, LONGINT, TIME:
		return 32
	case SHORTINT:
		return 16
	case BYTE:
		return 8
	case REAL, REALTIME:
		return 64
	default:
		return 0 // Unknown type
	}
}

func GetPortDirection(direction string) PortDirection {
	switch strings.ToLower(direction) {
	case "input":
		return INPUT
	case "output":
		return OUTPUT
	case "inout":
		return INOUT
	default:
		return INTERNAL // Default to internal if not specified
	}
}

var generalModuleRegex = regexp.MustCompile(
	`(?m)module\s+(\w+)\s*(?:#\s*\(([\s\S]*?)\))?\s*\(([\s\S]*?)\);\s((\s+.*)+)\sendmodule`,
)

var generalClassRegex = regexp.MustCompile(
	`(?m)(?:(virtual)\s+)?class\s+(\w+)\s*(?:extends\s+(\w+))?(?:\s+#\s*\(([\s\S]*?)\))?;\s((?:\s+.*)+)\sendclass`,
)

var generalStructRegex = regexp.MustCompile(
	`(?m)typedef\s+struct\s+(?:packed\s+)\{((?:\s+.*)+)\}\s+(\w+);`,
)

var variableRegexTemplate = `(?m)^\s*(?:\w+\s+)?(%s)\s+(?:((\[[\w\-]+:[\w\-]+\])+|unsigned)\s+)?(?:(?:(\w+),\s+)*(\w+))(?:\s+(\[.*\]))?(?:\s+=\s+new\(.*\))?;`

// TODO: #15 improve to replace the initial \w with rand local const ... and I don't know what not Also add the support for declarations with , for many decls
var generalVariableRegex = regexp.MustCompile(
	fmt.Sprintf(
		variableRegexTemplate,
		`reg|wire|integer|real|time|realtime|logic|bit|byte|shortint|int|longint|shortreal|string|struct|enum`,
	),
)

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

func matchModulesFromBytes(content []byte) [][]byte {
	return generalModuleRegex.FindSubmatch(content)
}

func MatchAllModulesFromString(content string) [][]string {
	return generalModuleRegex.FindAllStringSubmatch(content, -1)
}

func MatchAllClassesFromString(content string) [][]string {
	return generalClassRegex.FindAllStringSubmatch(content, -1)
}

func MatchAllStructsFromString(content string) [][]string {
	return generalStructRegex.FindAllStringSubmatch(content, -1)
}

func MatchAllVariablesFromString(content string) [][]string {
	return generalVariableRegex.FindAllStringSubmatch(content, -1)
}

func userDedinedVariablesRegex(verilogFile *VerilogFile) *regexp.Regexp {
	newTypes := []string{}
	for _, class := range verilogFile.Classes {
		newTypes = append(newTypes, class.Name)
	}
	for _, iface := range verilogFile.Interfaces {
		newTypes = append(newTypes, iface.Name)
	}
	for _, strct := range verilogFile.Structs {
		newTypes = append(newTypes, strct.Name)
	}
	newTypesConcat := strings.Join(newTypes, "|")
	regexpString := fmt.Sprintf(
		variableRegexTemplate,
		newTypesConcat,
	)
	return regexp.MustCompile(regexpString)
}

func matchUserDefinedVariablesFromString(vf *VerilogFile, content string) [][]string {
	return userDedinedVariablesRegex(vf).FindAllStringSubmatch(content, -1)
}

// TODO make the regex matching depend on thetypes we defined above
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
func parseRange(rangeStr string, parameters map[string]Parameter) (int, error) {
	// Handle common formats: [7:0], [WIDTH-1:0], etc.
	rangeStr = strings.TrimSpace(rangeStr)

	if rangeStr == "" {
		return 0, nil // No range means scalar (1-bit)
	}

	// --- Priority 1: Simple numeric case [N:0] ---
	simpleRangeRegex := regexp.MustCompile(`^\[\s*(\d+)\s*:\s*0\s*\]$`)
	if matches := simpleRangeRegex.FindStringSubmatch(rangeStr); len(matches) > 1 {
		var width int
		// Use Sscanf for safer parsing
		n, err := fmt.Sscanf(matches[1], "%d", &width)
		if err != nil || n != 1 {
			// Use default width 8 on error, but signal the error
			return 8, fmt.Errorf("invalid numeric range format: %s, defaulting to 8", rangeStr)
		}
		return width + 1, nil
	}

	// --- Priority 2: Parameter-based range: [PARAM-1:0] or [PARAM:0] ---
	// Regex now ensures the identifier starts with a non-digit character
	paramRangeRegex := regexp.MustCompile(`^\[\s*([a-zA-Z_]\w*)\s*(?:-\s*1)?\s*:\s*0\s*\]$`)
	if matches := paramRangeRegex.FindStringSubmatch(rangeStr); len(matches) > 1 {
		paramName := matches[1]
		if param, ok := parameters[paramName]; ok && param.DefaultValue != "" {
			// Attempt to convert parameter value to integer
			widthVal, err := strconv.Atoi(param.DefaultValue)
			if err == nil {
				if strings.Contains(matches[0], "-1") { // Matched [PARAM-1:0]
					return widthVal, nil // Width is the parameter value
				}
				// Matched [PARAM:0]
				return widthVal + 1, nil
			}
			// Parameter value is not a simple integer, fall through to other checks
			fmt.Printf(
				"Warning: Parameter '%s' value '%s' is not a simple integer for range '%s'.\n",
				paramName,
				param.DefaultValue,
				rangeStr,
			)
		} else {
			// Parameter not found or has no default value, fall through
			fmt.Printf("Warning: Parameter '%s' not found or has no value for range '%s'.\n", paramName, rangeStr)
		}
		// If parameter lookup failed (not found, no value, not int), fall through to heuristics/default
	}

	// --- Priority 3: Heuristics and Fallbacks ---

	// Add special handling for [31:0] which might be appearing in various formats
	// (This might be redundant now with the numeric check above, but keep as fallback)
	if strings.Contains(rangeStr, "31:0") || strings.Contains(rangeStr, "32-1:0") {
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

// TODO: #8 Use the thread safe version in utils/files.go and remove this file return
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
		generalMatches := matchModulesFromBytes(content)
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
func parsePortDeclaration(line string, parameters map[string]Parameter) (*Port, bool) {
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

	portType := GetPortType(strings.TrimSpace(matches[1]))
	signedStr := strings.TrimSpace(matches[2])
	rangeStr := strings.TrimSpace(matches[3])
	portName := strings.TrimSpace(matches[4])

	if portType == UNKNOWN {
		portType = LOGIC // Default type if not specified (SystemVerilog) or wire (Verilog)
	}
	isSigned := (signedStr == "signed")
	width, err := parseRange(rangeStr, parameters)
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
	if width == 0 && rangeStr == "" && err == nil {
		width = GetWidthForType(portType)
	}

	if width == 0 { // Ensure width is at least 1 (should not happen if parseRange guarantees >= 1)
		fmt.Printf(
			"Warning: Port '%s' ended up with width 0 after parsing.\n",
			portName,
		)
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

// extractANSIPortDeclarations parses the raw port list string from the module header.
// It handles ANSI style declarations within the header and creates placeholders for non-ANSI.
// Returns a map of port name to the parsed Port struct (or placeholder) and a slice maintaining the original order.
func extractANSIPortDeclarations(
	portListStr string,
	parameters map[string]Parameter,
) (map[string]Port, []string) {
	// TODO determine if the headerPortOrder is really usefull if not delete it
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
			portType := GetPortType(strings.TrimSpace(matches[2]))
			signedStr := strings.TrimSpace(matches[3])
			rangeStr := strings.TrimSpace(matches[4])
			portName = strings.TrimSpace(matches[5])

			isSigned := (signedStr == "signed")
			width, err := parseRange(rangeStr, parameters)
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
			direction := GetPortDirection(directionStr)

			// Handle default widths for types if no range specified AND parseRange didn't error
			if width == 1 && rangeStr == "" && err == nil {
				width = GetWidthForType(portType)
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
			port = Port{Name: portName, Width: 0, Type: UNKNOWN, Direction: INTERNAL, IsSigned: false} // Sensible defaults
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

// scanForPortDeclarationsFromReader scans the provided reader content to find detailed port declarations (non-ANSI style).
// It returns a map of port names to fully parsed Port structs found in the body.
func scanForPortDeclarationsFromReader(
	reader io.Reader, // Changed from *os.File to io.Reader
	targetModule string,
	parameters map[string]Parameter,
) (map[string]Port, error) {
	// No need to seek, scanner works directly with the reader from its current position
	scanner := bufio.NewScanner(reader)

	parsedPortsMap := make(map[string]Port) // Ports found in body scan

	inCommentBlock := false
	inModuleHeader := false // Track if we are between 'module ... (' and ');'
	inTargetModule := false // Track if we are inside the target module definition

	moduleStartRegex := regexp.MustCompile(
		"^\\s*module\\s+" + regexp.QuoteMeta(targetModule),
	)
	headerEndRegex := regexp.MustCompile(`\)\s*;`) // Matches the end of the port list ' );'
	moduleEndRegex := regexp.MustCompile(`^\s*endmodule`)

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
			if port, ok := parsePortDeclaration(strings.TrimSpace(lineBeforeHeaderEnd), parameters); ok {
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
			if port, ok := parsePortDeclaration(trimmedLine, parameters); ok {
				// Store the details found in the body, avoid overwriting if already found (first declaration wins)
				if _, exists := parsedPortsMap[port.Name]; !exists {
					parsedPortsMap[port.Name] = *port
				}
			}
		}
	}

	if err := scanner.Err(); err != nil {
		return nil, fmt.Errorf("error scanning content: %v", err) // Updated error message
	}

	return parsedPortsMap, nil
}

// extractNonANSIPortDeclarations scans the provided content for non-ANSI port declarations in the module content
func extractNonANSIPortDeclarations(
	content string,
	parameters map[string]Parameter,
) (map[string]Port, error) {
	scanner := bufio.NewScanner(strings.NewReader(content))
	parsedPortsMap := make(map[string]Port)

	inCommentBlock := false

	for scanner.Scan() {
		line := scanner.Text()

		// Handle multi-line comments
		if strings.Contains(line, "/*") {
			if !strings.Contains(line, "*/") {
				inCommentBlock = true
			}
			line = regexp.MustCompile(`/\*.*?\*/`).ReplaceAllString(line, "")
			line = regexp.MustCompile(`/\*.*`).ReplaceAllString(line, "")
		}
		if inCommentBlock {
			if strings.Contains(line, "*/") {
				inCommentBlock = false
				line = regexp.MustCompile(`.*\*/`).ReplaceAllString(line, "")
			} else {
				continue
			}
		}
		// Handle single-line comments
		line = regexp.MustCompile(`//.*`).ReplaceAllString(line, "")
		trimmedLine := strings.TrimSpace(line)

		if trimmedLine == "" {
			continue
		}

		// Attempt to parse the line as a port declaration
		if port, ok := parsePortDeclaration(trimmedLine, parameters); ok {
			if _, exists := parsedPortsMap[port.Name]; !exists {
				parsedPortsMap[port.Name] = *port
			}
		}
	}

	if err := scanner.Err(); err != nil {
		return nil, fmt.Errorf("error scanning content: %v", err)
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
		isPlaceholder := headerPort.Width == 0 && headerPort.Type == UNKNOWN &&
			headerPort.Direction == INTERNAL &&
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
			// TODO: #6 remove these fallback ports, all should be defined
			fallbackPort := Port{
				Name:      name,
				Direction: direction,
				Type:      UNKNOWN, // Default type
				Width:     0,       // Default to scalar
				IsSigned:  false,
			}
			portsToAdd = append(portsToAdd, fallbackPort)
			existingPorts[name] = true // Mark as added
		}
	}
	module.Ports = append(module.Ports, portsToAdd...)
}

// mergePortInfo combines information from header parsing and body scanning.
// It prioritizes details found in the body scan (non-ANSI) over header placeholders or potentially incomplete ANSI info.
func mergePortInfo(
	headerPorts map[string]Port,
	parsedPortsMap map[string]Port,
	headerPortOrder []string,
) []Port {
	finalPorts := []Port{}
	processedPorts := make(map[string]bool)

	for _, nameInHeader := range headerPortOrder {
		if processedPorts[nameInHeader] {
			continue // Already processed (e.g., duplicate name in header)
		}

		headerPort, foundInHeader := headerPorts[nameInHeader]
		bodyPort, foundInBody := parsedPortsMap[nameInHeader]

		if !foundInHeader {
			// This shouldn't happen if headerPortOrder comes from headerPorts keys, but handle defensively
			fmt.Printf("Warning: Port '%s' in order but not found in header map.\n", nameInHeader)
			continue
		}

		finalPort := headerPort // Start with header info

		// If found in body scan, these details are more accurate for non-ANSI or override header info
		if foundInBody {
			finalPort.Direction = bodyPort.Direction
			finalPort.Type = bodyPort.Type
			finalPort.Width = bodyPort.Width
			finalPort.IsSigned = bodyPort.IsSigned
		}

		// Final check for width=0 (shouldn't happen with parseRange defaulting to 1 or body scan)
		if finalPort.Width == 0 {
			fmt.Printf(
				"Warning: Port '%s' ended up with width 0 after merge. Setting to 1.\n",
				finalPort.Name,
			)
			finalPort.Width = 1
		}

		finalPorts = append(finalPorts, finalPort)
		processedPorts[nameInHeader] = true
	}

	// Add any ports found ONLY in the body scan (e.g., if header list was incomplete or malformed)
	// This is less common but possible.
	for nameInBody, bodyPort := range parsedPortsMap {
		if !processedPorts[nameInBody] {
			fmt.Printf(
				"Warning: Port '%s' found in body scan but not listed in header. Adding anyway.\n",
				nameInBody,
			)
			if bodyPort.Width == 0 { // Ensure width is valid
				bodyPort.Width = 1
			}
			finalPorts = append(finalPorts, bodyPort)
			processedPorts[nameInBody] = true
		}
	}

	return finalPorts
}

// Helper function to convert slice of Parameters to a map for easy lookup
func parametersToMap(params []Parameter) map[string]Parameter {
	paramMap := make(map[string]Parameter)
	for _, p := range params {
		paramMap[p.Name] = p
	}
	return paramMap
}

// Extract classes and modules from a SystemVerilog file
// TODO: delete this function and replace it with regex
func ExtractDefinitions(filePath string) (map[string]string, map[string]string, error) {
	fileContent, err := utils.ReadFileContent(filePath)
	if err != nil {
		return nil, nil, fmt.Errorf("failed to read file %s: %v", filePath, err)
	}
	thingName := ""
	var isModule bool
	var isClass bool

	lines := strings.Split(fileContent, "\n")
	allModules := make(map[string]string)
	allClasses := make(map[string]string)
	thingContent := []string{}

	for _, line := range lines {
		trimmedLine := strings.TrimSpace(line)
		switch {
		case strings.HasPrefix(trimmedLine, "module") || strings.HasPrefix(trimmedLine, "class"):
			// Extract module name, handle potential parameters/ports in declaration
			parts := strings.Fields(trimmedLine)
			if len(parts) >= 2 {
				namePart := parts[1]
				// Remove parameter list #(...) and port list (...) if present
				if idx := strings.IndexAny(namePart, "(#"); idx != -1 {
					namePart = namePart[:idx]
				}
				// Use base filename and extracted name for a unique key
				thingName = filepath.Base(filePath) + "_" + namePart
				thingContent = []string{line} // Start collecting with the module line itself
				switch {
				case strings.HasPrefix(trimmedLine, "module"):
					isModule = true
					isClass = false
				case strings.HasPrefix(trimmedLine, "class"):
					isModule = false
					isClass = true
				default:
					// Malformed line, reset state just in case
					return nil, nil, errors.New("Statement should never have been reached")
					// thingName = ""
					// thingContent = []string{}
					// isModule = false
					// isClass = false
				}
			} else {
				// Malformed module line, reset state just in case
				thingName = ""
				thingContent = []string{}
				isModule = false
				isClass = false
			}
		case strings.HasPrefix(trimmedLine, "endmodule") || strings.HasPrefix(trimmedLine, "endclass"):
			if thingName != "" { // Only process if we were inside a module
				thingContent = append(thingContent, line) // Add the endmodule line
				switch {
				case isModule && strings.HasPrefix(trimmedLine, "endmodule"):
					allModules[thingName] = strings.Join(thingContent, "\n")
				case isClass && strings.HasPrefix(trimmedLine, "endclass"):
					allClasses[thingName] = strings.Join(thingContent, "\n")
				default:
					return nil, nil, fmt.Errorf("Invalid end statement for %s", thingName)
				}
				// Reset for the next potential module
				thingName = ""
				thingContent = []string{}
			}
		default:
			if thingName != "" { // Only append lines if we are inside a module or a class definition
				thingContent = append(thingContent, line)
			}
			// Otherwise, ignore lines outside module definitions
		}
	}

	if len(allModules) == 0 {
		return nil, nil, fmt.Errorf("no modules or classes found in file %s", filePath)
	}

	return allModules, allClasses, nil
}

func GetDependenciesSnippetNeeds(snippet string) error { //nolint:revive
	return errors.New("GetDependenciesSnippetNeeds not implemented yet")
}

func (v *VerilogFile) ParseModules(moduleText string) error {
	allMatchedModule := MatchAllModulesFromString(moduleText)
	v.Modules = make(map[string]*Module)
	for _, matchedModule := range allMatchedModule {
		if len(matchedModule) < 5 {
			return errors.New("no module found in the provided text")
		}
		moduleName := matchedModule[1]
		paramListStr := matchedModule[2]
		portListStr := matchedModule[3]
		module := &Module{
			Name:       moduleName,
			Ports:      []Port{},
			Parameters: []Parameter{},
			Body:       matchedModule[4],
		}
		parameters, err := parseParameters(paramListStr)
		if err != nil {
			return fmt.Errorf("failed to parse parameters: %v", err)
		}
		module.Parameters = parameters
		err = parsePortsAndUpdateModule(portListStr, module)
		if err != nil {
			return fmt.Errorf("failed to parse ports: %v", err)
		}
		v.Modules[moduleName] = module
	}
	return nil
}

func (v *VerilogFile) ParseClasses(classText string) error {
	allMatchedClasses := MatchAllClassesFromString(classText)
	v.Classes = make(map[string]*Class)
	for _, matchedClass := range allMatchedClasses {
		if len(matchedClass) < 5 {
			return errors.New("no class found in the provided text")
		}
		isVirtual := matchedClass[1] == "virtual"
		className := matchedClass[2]
		extends := matchedClass[3]
		paramListStr := matchedClass[4]
		content := matchedClass[5]
		parameters, err := parseParameters(paramListStr)
		if err != nil {
			return fmt.Errorf("failed to parse parameters: %v", err)
		}
		class := &Class{
			Name:       className,
			Parameters: parameters,
			Body:       content,
			isVirtual:  isVirtual,
			extends:    extends,
		}
		v.Classes[className] = class
	}
	return nil
}

// TODO #9 : either merge this with the ExtractDefinitions or remove it
// ParseVerilogFile parses a Verilog file and extracts module information
func ParseVerilogFile(filename string, providedTargetModule string) (*Module, error) {
	file, content, err := openAndReadFile(filename)
	if err != nil {
		return nil, err
	}
	defer file.Close()

	targetModule := determineTargetModule(filename, providedTargetModule)

	// Find module declaration first to get the actual name and port list string
	actualTargetModule, paramListStr, portListStr, findErr := findModuleDeclaration(
		content,
		targetModule,
	)
	if findErr != nil {
		// Attempt fallback to find *any* module
		generalMatches := matchModulesFromBytes(content)
		if len(generalMatches) < 4 {
			return nil, fmt.Errorf(
				"no module found matching '%s' or any other name in file '%s': %w",
				targetModule,
				filename,
				findErr,
			)
		}
		fmt.Printf(
			"Warning: Target module '%s' not found in file '%s', parsing first module '%s' instead.\n",
			targetModule,
			filename,
			string(generalMatches[1]),
		)
		actualTargetModule = string(generalMatches[1])
		if len(generalMatches[2]) > 0 {
			paramListStr = string(generalMatches[2])
		} else {
			paramListStr = ""
		}
		if len(generalMatches[3]) > 0 {
			portListStr = string(generalMatches[3])
		} else {
			portListStr = ""
		}
	}

	module := &Module{
		Name:       actualTargetModule,
		Ports:      []Port{},
		Parameters: []Parameter{},
		Body:       string(content),
	}

	// Parse parameters
	if paramListStr != "" {
		params, err := parseParameters(paramListStr)
		if err != nil {
			return nil, fmt.Errorf("failed to parse parameters: %v", err)
		}
		module.Parameters = params
	}
	paramMap := parametersToMap(module.Parameters)

	// Parse header ports (ANSI or placeholders)
	headerPorts, headerPortOrder := extractANSIPortDeclarations(portListStr, paramMap)

	// Re-scan the file from the beginning for non-ANSI port declarations
	_, seekErr := file.Seek(0, 0)
	if seekErr != nil {
		return nil, fmt.Errorf("failed to seek file for non-ANSI scan: %v", seekErr)
	}
	parsedPortsMap, scanErr := scanForPortDeclarationsFromReader(
		file,
		actualTargetModule,
		paramMap,
	) // Pass the file object (io.Reader)
	if scanErr != nil {
		// Log warning but proceed, header info might be sufficient
		fmt.Printf("Warning: Error during scan for non-ANSI ports in '%s': %v\n", filename, scanErr)
		// Ensure parsedPortsMap is not nil
		if parsedPortsMap == nil {
			parsedPortsMap = make(map[string]Port)
		}
	}

	// Merge header and body scan information
	module.Ports = mergePortInfo(headerPorts, parsedPortsMap, headerPortOrder)

	// Apply fallback for ports that remained placeholders after merge
	applyPortDeclarationFallback(
		module,
		headerPorts,
		parsedPortsMap,
	) // Pass original headerPorts and parsedPortsMap

	// Final checks on parsed ports
	if len(module.Ports) == 0 && portListStr != "" {
		return nil, fmt.Errorf(
			"failed to parse any ports for module %s in file '%s' despite port list being present",
			actualTargetModule,
			filename,
		)
	} else if len(module.Ports) == 0 {
		fmt.Printf("Warning: No ports found or parsed for module %s in file '%s'. Module might have no ports.\n", actualTargetModule, filename)
	}

	return module, nil
}

// ParseVerilogContent parses Verilog content provided as bytes and extracts module information.
// It attempts to find the specified targetModule or the first module if targetModule is empty.
// The filename is used for context (e.g., error messages, default module name).
// TODO: merge it with the ParseVerilogFile function
func ParseVerilogContent(
	content []byte,
	targetModule string,
) (*Module, error) {
	// Find module declaration first
	actualTargetModule, paramListStr, portListStr, findErr := findModuleDeclaration(
		content,
		targetModule,
	)
	if findErr != nil {
		// Attempt fallback to find *any* module
		generalMatches := matchModulesFromBytes(content)
		if len(generalMatches) < 4 {
			return nil, fmt.Errorf(
				"no module found matching '%s' or any other name in content: %w",
				targetModule,
				findErr,
			)
		}
		fmt.Printf(
			"Warning: Target module '%s' not found in content, parsing first module '%s' instead.\n",
			targetModule,
			string(generalMatches[1]),
		)
		actualTargetModule = string(generalMatches[1])
		if len(generalMatches[2]) > 0 {
			paramListStr = string(generalMatches[2])
		} else {
			paramListStr = ""
		}
		if len(generalMatches[3]) > 0 {
			portListStr = string(generalMatches[3])
		} else {
			portListStr = ""
		}
	}

	module := &Module{
		Name:       actualTargetModule,
		Ports:      []Port{},
		Parameters: []Parameter{},
		Body:       string(content), // Store the original content parsed
	}

	// Parse parameters
	if paramListStr != "" {
		parameters, err := parseParameters(paramListStr)
		if err != nil {
			return nil, fmt.Errorf("failed to parse parameters: %v", err)
		}
		module.Parameters = parameters
	}
	paramMap := parametersToMap(module.Parameters)

	// Parse header ports (ANSI or placeholders)
	headerPorts, headerPortOrder := extractANSIPortDeclarations(portListStr, paramMap)

	// Scan the content for non-ANSI port declarations using a reader
	contentReader := bytes.NewReader(
		content,
	) // Create reader from byte slice
	parsedPortsMap, scanErr := scanForPortDeclarationsFromReader(
		contentReader,
		actualTargetModule,
		paramMap,
	) // Pass the reader
	if scanErr != nil {
		// Log warning but proceed
		fmt.Printf(
			"Warning: Error during scan for non-ANSI ports in content: %v\n",
			scanErr,
		)
		// Ensure parsedPortsMap is not nil
		if parsedPortsMap == nil {
			parsedPortsMap = make(map[string]Port)
		}
	}

	// Merge header and body scan information
	module.Ports = mergePortInfo(headerPorts, parsedPortsMap, headerPortOrder)

	// Apply fallback for ports that remained placeholders after merge
	applyPortDeclarationFallback(
		module,
		headerPorts,
		parsedPortsMap,
	) // Pass original headerPorts and parsedPortsMap

	// Final checks on parsed ports
	if len(module.Ports) == 0 && portListStr != "" {
		return nil, fmt.Errorf(
			"failed to parse any ports for module %s from content despite port list being present",
			actualTargetModule,
		)
	} else if len(module.Ports) == 0 {
		fmt.Printf("Warning: No ports found or parsed for module %s from content. Module might have no ports.\n", actualTargetModule)
	}

	return module, nil
}

// parseParameters extracts parameters from the module parameter list
func parseParameters(paramList string) ([]Parameter, error) {
	// Split by commas, but handle multi-line parameters carefully
	// A simple split might break if a value contains a comma (e.g., in string literal)
	// For now, assume simple comma separation works for typical parameter lists.
	// TODO: Improve splitting logic if needed for complex parameter values.
	params := strings.Split(paramList, ",")

	var parametersList []Parameter

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

			parametersList = append(parametersList, Parameter{
				Name:         paramName,
				Type:         paramType, // Will be "" if no type keyword was found
				DefaultValue: paramValue,
			})
		} else {
			return nil, fmt.Errorf("Could not parse parameter fragment: '%s'", param)
		}
	}
	return parametersList, nil
}

func parsePortsAndUpdateModule(portList string, module *Module) error {
	paramMap := parametersToMap(module.Parameters)

	headerPorts, headerPortOrder := extractANSIPortDeclarations(portList, paramMap)
	parsedPortsMap, scanErr := extractNonANSIPortDeclarations(
		module.Body,
		paramMap,
	)
	if scanErr != nil {
		fmt.Printf("Warning: Error during scan for non-ANSI ports: %v\n", scanErr)
		if parsedPortsMap == nil {
			parsedPortsMap = make(map[string]Port)
		}
	}

	// Merge header and body scan information
	module.Ports = mergePortInfo(headerPorts, parsedPortsMap, headerPortOrder)

	// Apply fallback for ports that remained placeholders after merge
	applyPortDeclarationFallback(
		module,
		headerPorts,
		parsedPortsMap,
	)

	if len(module.Ports) == 0 && portList != "" {
		return fmt.Errorf(
			"failed to parse any ports for module %s despite port list being present",
			module.Name,
		)
	} else if len(module.Ports) == 0 {
		fmt.Printf("Warning: No ports found or parsed for module %s. Module might have no ports.\n", module.Name)
	}
	return nil
}

// Be carefull must be parsed third after ParseClass and ParseStruct as the types of the variables might not be defined yet
func (v *VerilogFile) ParseVariables(
	content string,
) ([]*Variable, error) {
	allMatchedVariables := MatchAllVariablesFromString(content)
	variables := make([]*Variable, 0, len(allMatchedVariables))
	for _, matchedVariable := range allMatchedVariables {
		if len(matchedVariable) < 4 {
			return nil, errors.New("no variable found in the provided text")
		}
		varType := GetPortType(matchedVariable[1])
		widthStr := matchedVariable[3]
		width, err := parseRange(widthStr, nil)
		if err != nil {
			return nil, fmt.Errorf("failed to parse width: %v", err)
		}
		if width == 0 {
			width = GetWidthForType(varType)
		}
		var parentStruct *Struct
		var parentClass *Class
		if varType == UNKNOWN {
			// Check if it's a struct or class that we have already defined
			if _, exists := v.Structs[matchedVariable[1]]; exists {
				varType = USERDEFINED
				parentStruct = v.Structs[matchedVariable[1]]
			} else if _, exists := v.Classes[matchedVariable[1]]; exists {
				varType = USERDEFINED
				parentClass = v.Classes[matchedVariable[1]]
			} else {
				return nil, fmt.Errorf("unknown type '%s' for variable '%s'", matchedVariable[1], matchedVariable[3])
			}
		}
		unsigned := matchedVariable[2] == "unsigned"
		variableName := matchedVariable[3]
		variable := &Variable{
			Name:         variableName,
			Type:         varType,
			Width:        width,
			Unsigned:     unsigned,
			ParentStruct: parentStruct,
			ParentClass:  parentClass,
		}
		variables = append(variables, variable)
	}
	return variables, nil
}

func (v *VerilogFile) ParseStructs(
	content string,
	firstPass bool,
) error {
	if firstPass {
		v.Structs = make(map[string]*Struct)
	}
	allMatchedStructs := MatchAllStructsFromString(content)
	for _, matchedStruct := range allMatchedStructs {
		if len(matchedStruct) < 2 {
			return errors.New("no struct found in the provided text")
		}
		structName := matchedStruct[2]
		varList := matchedStruct[1]
		if firstPass {
			s := &Struct{
				Name: structName,
			}
			v.Structs[structName] = s
		} else {
			variables, err := v.ParseVariables(varList)
			if err != nil {
				return fmt.Errorf("failed to parse variables in struct '%s': %v", structName, err)
			}
			v.Structs[structName].Variables = variables
			for _, variable := range variables {
				if variable.Type == USERDEFINED {
					if variable.ParentStruct != nil {
						v.DependancyMap[structName].DependsOn = append(v.DependancyMap[structName].DependsOn, variable.ParentStruct.Name)
					}
					if variable.ParentClass != nil {
						v.DependancyMap[structName].DependsOn = append(v.DependancyMap[structName].DependsOn, variable.ParentClass.Name)
					}
				}
			}
		}
	}
	return nil
}

// Only parses the dependencies of the classes
// Probably overengineered and should only see if the name of a class or a struct just happens to be there but too late I already wrote it
func (v *VerilogFile) typeDependenciesParser() error {
	for _, class := range v.Classes {
		if class.isVirtual {
			v.DependancyMap[class.Name].DependsOn = append(
				v.DependancyMap[class.Name].DependsOn,
				class.extends,
			)
		}
		vars := matchUserDefinedVariablesFromString(v, class.Body)
		for _, matchedVariable := range vars {
			if len(matchedVariable) < 4 {
				return errors.New("no variable found in the provided text")
			}
			userTypeStr := matchedVariable[1]
			v.DependancyMap[class.Name].DependsOn = append(
				v.DependancyMap[class.Name].DependsOn,
				userTypeStr,
			)
		}
	}
	for _, module := range v.Modules {
		vars := matchUserDefinedVariablesFromString(v, module.Body)
		for _, matchedVariable := range vars {
			if len(matchedVariable) < 4 {
				return errors.New("no variable found in the provided text")
			}
			userTypeStr := matchedVariable[1]
			v.DependancyMap[module.Name].DependsOn = append(
				v.DependancyMap[module.Name].DependsOn,
				userTypeStr,
			)
		}
	}
	return nil
}

func (v *VerilogFile) createDependancyMap() {
	v.DependancyMap = make(map[string]*DependencyNode)
	for _, module := range v.Modules {
		v.DependancyMap[module.Name] = &DependencyNode{
			Name:      module.Name,
			DependsOn: []string{},
		}
	}
	for _, structName := range v.Structs {
		v.DependancyMap[structName.Name] = &DependencyNode{
			Name:      structName.Name,
			DependsOn: []string{},
		}
	}
	for _, className := range v.Classes {
		v.DependancyMap[className.Name] = &DependencyNode{
			Name:      className.Name,
			DependsOn: []string{},
		}
	}
}

func ParseVerilog(content string) (*VerilogFile, error) {
	verilogFile := &VerilogFile{}
	err := verilogFile.ParseStructs(content, true)
	if err != nil {
		return nil, fmt.Errorf("failed to parse structs: %v", err)
	}
	err = verilogFile.ParseClasses(content)
	if err != nil {
		return nil, fmt.Errorf("failed to parse classes: %v", err)
	}
	err = verilogFile.ParseStructs(content, false)
	if err != nil {
		return nil, fmt.Errorf("failed to parse structs: %v", err)
	}
	err = verilogFile.ParseModules(content)
	if err != nil {
		return nil, fmt.Errorf("failed to parse modules: %v", err)
	}
	verilogFile.createDependancyMap()
	err = verilogFile.typeDependenciesParser()
	if err != nil {
		return nil, fmt.Errorf("failed to parse dependencies: %v", err)
	}
	return verilogFile, nil
}
