package verilog

import (
	"bufio"
	"errors"
	"fmt"
	"regexp"
	"strconv"
	"strings"

	"github.com/toby-bro/pfuzz/pkg/utils"
	"golang.org/x/exp/maps"
)

var logger *utils.DebugLogger

// TODO: #5 Improve the type for structs, enums, userdefined types...
func getType(portTypeString string) PortType {
	// Extract the first word (type keyword) from the string
	// Handle cases like "logic [7:0] data" -> extract "logic"
	typeString := strings.TrimSpace(portTypeString)
	if typeString == "" {
		return LOGIC // Default for empty type
	}

	// Check if it's an interface type (contains a dot)
	if strings.Contains(typeString, ".") {
		return INTERFACE
	}

	// Extract the first word which should be the type keyword
	words := strings.Fields(typeString)
	if len(words) == 0 {
		return LOGIC // Default
	}

	firstWord := strings.ToLower(words[0])

	switch firstWord {
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
	case "logic", "":
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
	case "type":
		return TYPE
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
		return 0
	}
}

func getPortDirection(direction string) PortDirection {
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

// getInterfacePortDirection determines the direction of an interface port based on modport naming conventions
// and explicit direction. If explicit direction is provided, it takes precedence.
func getInterfacePortDirection(explicitDirection string) PortDirection {
	// If explicit direction is provided, use it
	if explicitDirection != "" {
		return getPortDirection(explicitDirection)
	}

	// For interface ports, the direction refers to whether the interface instance
	// is input or output to the module, not the signal directions within the interface.
	// By default, interface instances are typically inputs to modules (interface connections)
	return INPUT // Default to input for interface ports when not explicitly specified
}

var generalModuleRegex = regexp.MustCompile(fmt.Sprintf(
	`(?ms)^module\s+(\w+)\s*(?:#\s*\(([\s\S]*?)\))?\s*\((.*?)\);((?:\s*(?:%s)*)*)\s*endmodule`,
	utils.NegativeLookAhead("endmodule"),
))

var generalClassRegex = regexp.MustCompile(fmt.Sprintf(
	`(?m)^(?:(virtual)\s+)?class\s+(\w+)\s*(?:extends\s+(\w+))?(?:\s+#\s*\(([\s\S]*?)\))?;\s((?:\s*(?:%s)*)*)\s*endclass`,
	utils.NegativeLookAhead("endclass"),
))

var generalStructRegex = regexp.MustCompile(
	`(?m)^typedef\s+struct\s+(?:packed\s+)\{((?:\s+.*)+)\}\s+(\w+);`,
)

var generalInterfaceRegex = regexp.MustCompile(fmt.Sprintf(
	`(?m)^(?:(virtual)\s+)?interface\s+(\w+)\s*(?:#\s*\(([\s\S]*?)\))?\s*(?:extends\s+(\w+))?\s*(?:\(\s*([\s\S]*?)\)\s*)?;\s*((?:\s*(?:%s)*)*)\s*endinterface`,
	utils.NegativeLookAhead("endinterface"),
))

var generalPackageRegex = regexp.MustCompile(fmt.Sprintf(
	`(?m)^package\s+(\w+)\s*;\s*((?:\s*(?:%s)*)*)\s*endpackage`,
	utils.NegativeLookAhead("endpackage"),
))

var importRegex = regexp.MustCompile(`(?m)^.*import\s+.*$`)

var baseTypes = `reg|wire|integer|real|time|realtime|logic|bit|byte|shortint|int|longint|shortreal|string|struct|enum|type`

var widthRegex = `\[\s*[\w\(\)'\-\+\:\s]+\s*\]`

var baseTypesRegex = regexp.MustCompile(fmt.Sprintf(`(?m)^\s*(%s)\s*$`, baseTypes))

var variableRegexTemplate = `(?m)^(\s*)` +
	`(?:\w+\s+)?` +
	`(%s)\s+` +
	`(?:(?:(%s)+|(unsigned))\s+)?` +
	`(?:#\(\w+\)\s+)?` +
	`((?:(?:(?:\w+(?:\s+\[[^\]]+\])?\s*,\s*)+)\s*)*` +
	`(?:\w+(?:\s+\[[^\]]+\])?))(?:\s+=\s+(?:new\([^\)]*\)|null))?\s*;`

var pragmaString = `(?:\(\*([^\*]*)\*\))`

var generalPortRegex = regexp.MustCompile(fmt.Sprintf(
	`^\s*%s?\s*(input|output|inout)\s+(?:(%s)\s+)?(?:(signed|unsigned)\s+)?(\s*%s)?\s*(\w+)\s*(?:,|;)`,
	pragmaString,
	baseTypes,
	widthRegex,
))

var generalParameterRegex = regexp.MustCompile(
	`(?m)^\s*(?:(localparam|parameter)\s+)?` +
		fmt.Sprintf(`(?:(%s)\s+)?`, baseTypes) +
		fmt.Sprintf(`(?:\s*(%s)\s+)?`, widthRegex) +
		`(?:(?:unsigned|signed)\s+)?` +
		`(\w+)` +
		`(?:\s*(=)\s*(.*?))?` +
		`\s*(?:,|;)?$`,
)

var arrayRegex = regexp.MustCompile(`(?m)(\w+)(?:\s+(\[[^\]:]+\]))?`)

// Regex for general [MSB:LSB] range structure
var literalValueRangeRegex = regexp.MustCompile(`(?m)^\[\s*(.+)\s*:\s*(.+)\s*\]$`)

// Regex for parsing Verilog-style based literals (e.g., 12'hFAB, 'b10, 8'd255)
var verilogBasedLiteralRegex = regexp.MustCompile(
	`^\(?(?:(\d+)?\s*')?([bodhBODH])\s*([0-9a-fA-F_]+)\)?$`,
)

var ansiPortRegex = regexp.MustCompile(fmt.Sprintf(
	`^\s*%s?\s*(?:(input|output|inout)\s+)?(?:(`+
		baseTypes+
		`)\s+)?(?:(signed|unsigned)\s+)?`+
		`(?:(\[\s*[\w\-\+\:\s]+\s*\])\s+)?`+
		`(\w+)\s*`+
		`(?:\s*\[([^\]:])*\])?\s*$`, pragmaString),
)

// Regex for interface port declarations (e.g., "simple_bus.slave port_name")
var interfacePortRegex = regexp.MustCompile(fmt.Sprintf(
	`^\s*%s?\s*(?:(input|output|inout)\s+)?(\w+)\.(\w+)\s+(\w+)\s*(?:\s*\[([^\]:])*\])?\s*;?\s*$`,
	pragmaString,
))

var simplePortRegex = regexp.MustCompile(
	`^\s*(?:\.\s*(\w+)\s*\()?\s*(\w+)\s*\)?\s*$`,
)

var typedefRegex = regexp.MustCompile(fmt.Sprintf(
	`(?sm)^typedef(?:(?:\s+(?:struct|union|enum))?(?:\s+(?:packed|tagged))?)?(?:\s+(?:%s))?(?:\s*%s)?\s*([^{};]*?|\{[^{}]*?\})\s+(\w+)(?:\[[^\]]\])?;`,
	baseTypes,
	widthRegex,
))

// TODO: #15 improve to replace the initial \w with rand local const ... and I don't know what not Also add the support for declarations with , for many decls
var generalVariableRegex = regexp.MustCompile(
	fmt.Sprintf(
		variableRegexTemplate,
		baseTypes,
		widthRegex,
	),
)

var (
	scopeChangeRegex = regexp.MustCompile(`^\s*(function|task|always|class|clocking)`)
	taskClassRegex   = regexp.MustCompile(`^\s*(task|class)\b`)
)

// Interface modport patterns for interface port declarations
var ModportRegex = regexp.MustCompile(
	`(?s)(?:^|\s)modport\s+(\w+)\s*\((.*?)\)\s*;`,
)

var ModportPortRegex = regexp.MustCompile(
	`(?s)(input|output|inout|ref)\s+(.*?)(?:,|$)`,
)

// Regex patterns for detecting blocking constructs
var (
	assignRegex            = regexp.MustCompile(`(?m)^\s*assign\s+(\w+)`)
	wireAssignRegex        = regexp.MustCompile(`(?m)^\s*wire\s+(?:[^;=]*\s+)?(\w+)\s*=`)
	forceRegex             = regexp.MustCompile(`(?m)^\s*force\s+(\w+)`)
	alwaysCombRegex        = regexp.MustCompile(`(?s)always_comb\s*begin(.*?)end`)
	alwaysFFRegex          = regexp.MustCompile(`(?s)always_ff\s*@\([^)]*\)\s*begin(.*?)end`)
	alwaysRegex            = regexp.MustCompile(`(?s)always\s*@\([^)]*\)\s*begin(.*?)end`)
	blockingAssignRegex    = regexp.MustCompile(`(?m)^\s*(\w+)\s*(?:\[[^\]]*\])?\s*(?:<=|=)`)
	nonBlockingAssignRegex = regexp.MustCompile( // nolint: unused
		`(?m)^\s*(\w+)\s*(?:\[[^\]]*\])?\s*<=`,
	)
	moduleInstRegex = regexp.MustCompile(
		`(?m)^\s*(\w+)\s+(\w+)\s*\(((?:[^()]|\([^)]*\))*)\)\s*;`,
	)
	portConnectionRegex = regexp.MustCompile(`\.(\w+)\s*\(\s*(\w+)\s*\)`)
)

// ===============================================
// End of Advanced SystemVerilog Construct Patterns
// ===============================================

func matchAllModulesFromString(content string) [][]string {
	return generalModuleRegex.FindAllStringSubmatch(content, -1)
}

func matchAllClassesFromString(content string) [][]string {
	return generalClassRegex.FindAllStringSubmatch(content, -1)
}

func matchAllStructsFromString(content string) [][]string {
	return generalStructRegex.FindAllStringSubmatch(content, -1)
}

func matchAllInterfacesFromString(content string) [][]string {
	return generalInterfaceRegex.FindAllStringSubmatch(content, -1)
}

func matchAllPackagesFromString(content string) [][]string {
	return generalPackageRegex.FindAllStringSubmatch(content, -1)
}

func matchAllVariablesFromString(content string) [][]string { //nolint: unused
	return generalVariableRegex.FindAllStringSubmatch(content, -1)
}

func matchArraysFromString(content string) []string {
	return arrayRegex.FindStringSubmatch(content)
}

func matchAllTypedefsFromString(content string) [][]string {
	return typedefRegex.FindAllStringSubmatch(content, -1)
}

func userDefinedVariablesRegex(verilogFile *VerilogFile) *regexp.Regexp {
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
	for _, typedef := range verilogFile.Typedefs {
		newTypes = append(newTypes, typedef.Name)
	}
	newTypesConcat := strings.Join(newTypes, "|")
	regexpString := fmt.Sprintf(
		variableRegexTemplate,
		newTypesConcat,
		widthRegex,
	)
	return regexp.MustCompile(regexpString)
}

func matchUserDefinedVariablesFromString(vf *VerilogFile, content string) [][]string {
	if len(vf.Classes) == 0 && len(vf.Interfaces) == 0 && len(vf.Structs) == 0 &&
		len(vf.Typedefs) == 0 {
		return [][]string{}
	}
	return userDefinedVariablesRegex(vf).FindAllStringSubmatch(content, -1)
}

func matchAllParametersFromString(param string) []string {
	return generalParameterRegex.FindStringSubmatch(param)
}

func parseVerilogLiteral(literalStr string) (int64, error) {
	literalStr = strings.TrimSpace(literalStr)

	parts := verilogBasedLiteralRegex.FindStringSubmatch(literalStr)

	if len(parts) > 0 { // Matches format like 12'hFAB, 'hFAB (based literal)
		// parts[0] is full match
		// parts[1] is optional size (e.g., "12") - not strictly needed for the value itself
		// parts[2] is base character (e.g., "h")
		// parts[3] is the number string (e.g., "FAB")
		baseChar := strings.ToLower(parts[2])
		valueStr := strings.ReplaceAll(parts[3], "_", "") // Remove underscores for parsing

		var base int
		switch baseChar {
		case "b":
			base = 2
		case "o":
			base = 8
		case "d":
			base = 10
		case "h":
			base = 16
		default:
			// Should not happen if regex matches correctly
			return 0, fmt.Errorf("internal error: unknown base character '%s' from regex", baseChar)
		}

		val, err := strconv.ParseInt(valueStr, base, 64)
		if err != nil {
			return 0, fmt.Errorf(
				"failed to parse based literal value '%s' (original: '%s') with base %d: %v",
				valueStr,
				literalStr,
				base,
				err,
			)
		}
		return val, nil
	}
	// Not a based literal, attempt to parse as a simple decimal integer.
	// Underscores are allowed in Verilog numbers, e.g., 1_000_000.
	cleanedDecimalStr := strings.ReplaceAll(literalStr, "_", "")
	val, err := strconv.ParseInt(cleanedDecimalStr, 10, 64)
	if err != nil {
		// If it's not a based literal and not a simple decimal, it's an error for this function.
		// It might be a parameter name or an expression, which this function is not meant to parse.
		return 0, fmt.Errorf(
			"failed to parse '%s' as a Verilog-style based literal or simple decimal integer: %v",
			literalStr,
			err,
		)
	}
	return val, nil // Successfully parsed as simple decimal
}

// Utility functions for bit width parsing
func parseRange(rangeStr string, parameters map[string]*Parameter) (int, error) {
	// Handle common formats: [7:0], [WIDTH-1:0], etc.
	rangeStr = strings.TrimSpace(rangeStr)

	if rangeStr == "" {
		return 0, nil // No range means scalar (1-bit)
	}

	// --- Priority 1: Literal-based or simple numeric range: [MSB_LITERAL:LSB_LITERAL] or [N:M] ---
	if matches := literalValueRangeRegex.FindStringSubmatch(rangeStr); len(matches) > 2 {
		msbStr := matches[1]
		lsbStr := matches[2]

		msbVal, errMsb := parseVerilogLiteral(msbStr)
		lsbVal, errLsb := parseVerilogLiteral(lsbStr)

		if errMsb == nil && errLsb == nil { // Both parts successfully parsed as literals
			if msbVal < lsbVal {
				return 8, fmt.Errorf(
					"invalid literal range in '%s': MSB (%d) < LSB (%d), defaulting to 8",
					rangeStr,
					msbVal,
					lsbVal,
				)
			}
			return int(msbVal-lsbVal) + 1, nil
		}
		// If one or both parts failed to parse as literals, fall through to other parsing rules (e.g., parameters).
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
			logger.Warn(
				"Parameter '%s' value '%s' is not a simple integer for range '%s'.",
				paramName,
				param.DefaultValue,
				rangeStr,
			)
		} else {
			logger.Warn("Parameter '%s' not found or has no value for range '%s'.", paramName, rangeStr)
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

// parsePortDeclaration attempts to parse a line as a non-ANSI port declaration.
// It returns the parsed Port and true if successful, otherwise nil and false.
func parsePortDeclaration(
	line string,
	parameters map[string]*Parameter,
	variables map[string]*Variable,
) (*Port, bool) {
	var matches []string
	var direction PortDirection

	line = strings.TrimSpace(line) // Ensure leading/trailing whitespace is removed

	// First, try to match interface port (e.g., "simple_bus.slave port_name")
	interfaceMatches := interfacePortRegex.FindStringSubmatch(line)
	if len(interfaceMatches) == 7 {
		pragma := strings.TrimSpace(interfaceMatches[1])
		directionStr := strings.TrimSpace(interfaceMatches[2])
		interfaceName := strings.TrimSpace(interfaceMatches[3])
		modportName := strings.TrimSpace(interfaceMatches[4])
		portName := strings.TrimSpace(interfaceMatches[5])
		arrayStr := strings.TrimSpace(interfaceMatches[6])

		// Determine direction based on explicit direction or modport naming convention
		direction = getInterfacePortDirection(directionStr)

		port := &Port{
			Name:            portName,
			Direction:       direction,
			Type:            INTERFACE,
			Width:           0, // Interface ports don't have explicit width
			IsSigned:        false,
			AlreadyDeclared: false,
			Array:           arrayStr,
			InterfaceName:   interfaceName,
			ModportName:     modportName,
			Pragma:          pragma,
		}

		return port, true
	}

	// If not an interface port, try regular port parsing
	matches = generalPortRegex.FindStringSubmatch(line)
	if len(matches) != 7 {
		return nil, false // Not a matching port declaration line
	}
	pragma := strings.TrimSpace(matches[1])
	direction = getPortDirection(strings.TrimSpace(matches[2]))
	portTypeStr := strings.TrimSpace(matches[3])
	portType := getType(portTypeStr)
	signedStr := strings.TrimSpace(matches[4])
	rangeStr := strings.TrimSpace(matches[5])
	portName := strings.TrimSpace(matches[6])

	alreadyDeclared := false

	if _, exists := variables[portName]; exists && portTypeStr == "" {
		portType = variables[portName].Type
		alreadyDeclared = true
	}

	if portType == UNKNOWN {
		portType = LOGIC // Default type if not specified (SystemVerilog) or wire (Verilog)
	}
	isSigned := (signedStr == "signed")
	width, err := parseRange(rangeStr, parameters)
	if err != nil {
		// If parseRange returns an error, use the returned default width (e.g., 8)
		// but still log the original error message.
		logger.Warn(
			"Could not parse range '%s' for port '%s'. Using default width %d. Error: %v",
			rangeStr,
			portName,
			width, // Use the width returned by parseRange (the default)
			err,
		)
	}

	port := &Port{
		Name:            portName,
		Direction:       direction,
		Type:            portType,
		Width:           width,
		IsSigned:        isSigned,
		AlreadyDeclared: alreadyDeclared,
		InterfaceName:   "", // Regular ports don't have interface info
		ModportName:     "",
		Pragma:          pragma,
	}

	return port, true
}

// extractANSIPortDeclarations parses the raw port list string from the module header.
// It handles ANSI style declarations within the header and creates placeholders for non-ANSI.
// Returns a map of port name to the parsed Port struct (or placeholder) and a slice maintaining the original order.
func extractANSIPortDeclarations(
	portListStr string,
	parameters map[string]*Parameter,
) (map[string]*Port, []string) {
	headerPorts := make(map[string]*Port)
	headerPortOrder := []string{}

	for _, p := range strings.Split(portListStr, ",") {
		portDecl := strings.TrimSpace(p)
		if portDecl == "" {
			continue
		}

		portName := ""
		var port Port

		// First check for interface port declaration (e.g., "simple_bus.slave port_name")
		if interfaceMatches := interfacePortRegex.FindStringSubmatch(portDecl); len(
			interfaceMatches,
		) == 7 {
			pragma := strings.TrimSpace(interfaceMatches[1])
			directionStr := strings.TrimSpace(interfaceMatches[2])
			interfaceName := strings.TrimSpace(interfaceMatches[3])
			modportName := strings.TrimSpace(interfaceMatches[4])
			portName = strings.TrimSpace(interfaceMatches[5])
			arrayStr := strings.TrimSpace(interfaceMatches[6])

			// Determine direction based on explicit direction or modport naming convention
			direction := getInterfacePortDirection(directionStr)

			port = Port{
				Name:          portName,
				Direction:     direction,
				Type:          INTERFACE,
				Width:         0, // Interface ports don't have explicit width
				IsSigned:      false,
				Array:         arrayStr,
				InterfaceName: interfaceName,
				ModportName:   modportName,
				Pragma:        pragma,
			}
		} else if matches := ansiPortRegex.FindStringSubmatch(portDecl); len(matches) > 6 {
			// Full ANSI declaration found
			pragma := strings.TrimSpace(matches[1])
			directionStr := strings.TrimSpace(matches[2])
			portStr := strings.TrimSpace(matches[3])
			portType := getType(portStr)
			signedStr := strings.TrimSpace(matches[4])
			rangeStr := strings.TrimSpace(matches[5])
			portName = strings.TrimSpace(matches[6])
			array := strings.TrimSpace(matches[7])

			if directionStr == "" && portStr == "" && signedStr == "" && rangeStr == "" {
				if len(headerPortOrder) == 0 {
					logger.Debug("Header port declaration '%s' is empty.", portDecl)
					if matches := simplePortRegex.FindStringSubmatch(portDecl); len(matches) <= 2 {
						continue
					}
					// Simple name found (likely non-ANSI or Verilog-1995) or .name(signal)
					if matches[1] != "" { // .name(signal) case
						portName = matches[1]
					} else { // simple name case
						portName = matches[2]
					}
					// Create a placeholder, details expected in body scan
					port = Port{
						Name:          portName,
						Width:         0,
						Type:          UNKNOWN,
						Direction:     INTERNAL,
						IsSigned:      false,
						InterfaceName: "",
						ModportName:   "",
					} // Sensible defaults
				} else {
					// Port is the same as the last port
					precedingPort := headerPorts[headerPortOrder[len(headerPortOrder)-1]]
					port = Port{
						Name:          portName,
						Direction:     precedingPort.Direction,
						Type:          precedingPort.Type,
						Width:         precedingPort.Width,
						IsSigned:      precedingPort.IsSigned,
						Array:         precedingPort.Array,
						InterfaceName: precedingPort.InterfaceName,
						ModportName:   precedingPort.ModportName,
					}
				}
			} else {
				isSigned := (signedStr == "signed")
				width, err := parseRange(rangeStr, parameters)
				if err != nil {
					// Use the default width returned by parseRange on error
					logger.Warn(
						"Header parseRange failed for '%s' (%s): Using default width %d. Error: %v.",
						portName,
						rangeStr,
						width, // Use the width returned by parseRange (the default)
						err,
					)
				}

				// Determine direction
				direction := getPortDirection(directionStr)

				// Handle default widths for types if no range specified AND parseRange didn't error
				if false && width == 1 && rangeStr == "" && err == nil {
					width = GetWidthForType(portType)
				}

				port = Port{
					Name:          portName,
					Direction:     direction,
					Type:          portType,
					Width:         width,
					IsSigned:      isSigned,
					Array:         array,
					InterfaceName: "", // Regular ports don't have interface info
					ModportName:   "",
					Pragma:        pragma,
				}
			}
		} else if matches := simplePortRegex.FindStringSubmatch(portDecl); len(matches) > 2 {
			// Simple name found (likely non-ANSI or Verilog-1995) or .name(signal)
			if matches[1] != "" { // .name(signal) case
				portName = matches[1]
			} else { // simple name case
				portName = matches[2]
			}
			// Create a placeholder, details expected in body scan
			port = Port{
				Name:          portName,
				Width:         0,
				Type:          UNKNOWN,
				Direction:     INTERNAL,
				IsSigned:      false,
				InterfaceName: "",
				ModportName:   "",
			} // Sensible defaults
		} else {
			logger.Warn("Could not parse port declaration fragment in header: '%s'", portDecl)
			continue // Skip if we can't extract a name
		}

		if portName != "" {
			if _, exists := headerPorts[portName]; exists {
				logger.Warn(
					"Duplicate port name '%s' detected in module header.",
					portName,
				)
			}
			headerPorts[portName] = &port // Store parsed/placeholder port
			headerPortOrder = append(headerPortOrder, portName)
		}
	}

	return headerPorts, headerPortOrder
}

// extractNonANSIPortDeclarations scans the provided content for non-ANSI port declarations in the module content
func extractNonANSIPortDeclarations(
	content string,
	parameters map[string]*Parameter,
) (map[string]*Port, error) {
	paramList := []*Parameter{}
	for _, param := range parameters {
		paramList = append(paramList, param)
	}
	scanner := bufio.NewScanner(strings.NewReader(content))
	parsedPortsMap := make(map[string]*Port)

	parsedVariables := make(map[string]*Variable)

	for scanner.Scan() {
		trimmedLine := strings.TrimSpace(scanner.Text())
		if trimmedLine == "" {
			continue
		}
		if matched := scopeChangeRegex.MatchString(trimmedLine); matched {
			break
		}
		newParsedVariables, err := ParseVariables(nil, trimmedLine, paramList)
		if err != nil {
			return nil, fmt.Errorf("error parsing variables: %v", err)
		}
		maps.Copy(parsedVariables, newParsedVariables)
		port, ok := parsePortDeclaration(trimmedLine, parameters, parsedVariables)
		if ok {
			if _, exists := parsedPortsMap[port.Name]; !exists {
				parsedPortsMap[port.Name] = port
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
	headerPorts map[string]*Port,
	parsedPortsMap map[string]*Port,
) {
	portsToAdd := []*Port{}
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
			logger.Warn(
				" Port '%s' listed in header but not defined in body. Applying fallback naming convention.",
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
			fallbackPort := &Port{
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
// This version merges the two maps directly, and the order of the resulting ports is not guaranteed.
func mergePortInfo(
	headerPorts map[string]*Port,
	parsedPortsMap map[string]*Port,
) []*Port {
	finalPortsMap := make(map[string]*Port)

	// Add all ports from headerPorts first
	for name, port := range headerPorts {
		finalPortsMap[name] = port
	}

	// Then, merge/override with ports from parsedPortsMap
	for name, bodyPort := range parsedPortsMap {
		if headerPort, exists := finalPortsMap[name]; exists {
			// Port exists in both, bodyPort details take precedence
			finalPort := headerPort // Start with header info
			if bodyPort.Direction != INTERNAL {
				finalPort.Direction = bodyPort.Direction
			}
			if bodyPort.Type != UNKNOWN {
				finalPort.Type = bodyPort.Type
			}
			if bodyPort.Width > 0 {
				finalPort.Width = bodyPort.Width
			}
			if bodyPort.Array != "" {
				finalPort.Array = bodyPort.Array
			}
			if bodyPort.InterfaceName != "" {
				finalPort.InterfaceName = bodyPort.InterfaceName
			}
			if bodyPort.ModportName != "" {
				finalPort.ModportName = bodyPort.ModportName
			}
			finalPort.IsSigned = bodyPort.IsSigned
			finalPortsMap[name] = finalPort
		} else {
			// Port only exists in parsedPortsMap (body scan)
			finalPortsMap[name] = bodyPort
		}
	}

	// Convert map to slice
	finalPorts := make([]*Port, 0, len(finalPortsMap))
	for _, port := range finalPortsMap {
		finalPorts = append(finalPorts, port)
	}

	return finalPorts
}

// extractNonANSIParameterDeclarations scans the provided content for non-ANSI parameter declarations in the module body
func extractNonANSIParameterDeclarations(
	content string,
) ([]*Parameter, error) {
	scanner := bufio.NewScanner(strings.NewReader(content))
	bodyParameters := []*Parameter{}

	for scanner.Scan() {
		trimmedLine := strings.TrimSpace(scanner.Text())
		if trimmedLine == "" {
			continue
		}
		// Stop parsing when we hit a scope change (function, task, always, etc.)
		if matched := scopeChangeRegex.MatchString(trimmedLine); matched {
			break
		}

		// Check if line contains parameter or localparam declaration
		if strings.Contains(trimmedLine, "parameter") ||
			strings.Contains(trimmedLine, "localparam") {
			params, err := parseParameters(trimmedLine, false)
			if err != nil {
				logger.Warn("Failed to parse parameter line '%s': %v", trimmedLine, err)
				continue
			}
			bodyParameters = append(bodyParameters, params...)
		}
	}

	if err := scanner.Err(); err != nil {
		return nil, fmt.Errorf("error scanning content for parameters: %v", err)
	}

	return bodyParameters, nil
}

// mergeParameterInfo combines parameters from header (ANSI style) and body (non-ANSI style)
// Header parameters are marked as AnsiStyle=true, body parameters as AnsiStyle=false
// If a parameter exists in both places, the body declaration takes precedence for the value
func mergeParameterInfo(headerParams []*Parameter, bodyParams []*Parameter) []*Parameter {
	paramMap := make(map[string]*Parameter)
	finalParams := []*Parameter{}

	// First, add all header parameters
	for _, param := range headerParams {
		param.AnsiStyle = true
		paramMap[param.Name] = param
	}

	// Then, merge/override with body parameters
	for _, bodyParam := range bodyParams {
		bodyParam.AnsiStyle = false
		if headerParam, exists := paramMap[bodyParam.Name]; exists {
			// Parameter exists in both, merge information
			// Keep header type if body type is unknown, otherwise use body
			if bodyParam.Type == UNKNOWN && headerParam.Type != UNKNOWN {
				bodyParam.Type = headerParam.Type
			}
			// Body parameter value takes precedence
			paramMap[bodyParam.Name] = bodyParam
		} else {
			// Parameter only exists in body
			paramMap[bodyParam.Name] = bodyParam
		}
	}

	// Convert map back to slice, maintaining order (header first, then body-only)
	addedParams := make(map[string]bool)

	// First add header parameters (maintaining original order)
	for _, param := range headerParams {
		if finalParam, exists := paramMap[param.Name]; exists {
			finalParams = append(finalParams, finalParam)
			addedParams[param.Name] = true
		}
	}

	// Then add body-only parameters
	for _, param := range bodyParams {
		if !addedParams[param.Name] {
			finalParams = append(finalParams, paramMap[param.Name])
		}
	}

	return finalParams
}

// Helper function to convert slice of Parameters to a map for easy lookup
func parametersToMap(params []*Parameter) map[string]*Parameter {
	paramMap := make(map[string]*Parameter)
	for _, p := range params {
		paramMap[p.Name] = p
	}
	return paramMap
}

func (v *VerilogFile) parseModules(moduleText string) error {
	allMatchedModule := matchAllModulesFromString(moduleText)
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
			Ports:      []*Port{},
			Parameters: []*Parameter{},
			Body:       matchedModule[4],
		}

		// Parse header parameters (ANSI style)
		headerParameters, err := parseParameters(paramListStr, true)
		if err != nil {
			return fmt.Errorf("failed to parse header parameters: %v", err)
		}

		// Parse body parameters (non-ANSI style)
		bodyParameters, err := extractNonANSIParameterDeclarations(module.Body)
		if err != nil {
			logger.Warn("Error parsing body parameters for module %s: %v", moduleName, err)
			bodyParameters = []*Parameter{} // Continue with empty body parameters
		}

		// Merge header and body parameters
		module.Parameters = mergeParameterInfo(headerParameters, bodyParameters)

		err = parsePortsAndUpdateModule(portListStr, module)
		if err != nil {
			logger.Warn("Skipping %s as failed to parse ports: %v", moduleName, err)
			continue // Skip this module if port parsing fails
		}
		v.Modules[moduleName] = module
	}
	return nil
}

func (v *VerilogFile) parseClasses(classText string) error {
	allMatchedClasses := matchAllClassesFromString(classText)
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
		parameters, err := parseParameters(paramListStr, true)
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

func inferTypeFromDefaultValue(defaultValue string) PortType {
	trimmedVal := strings.TrimSpace(defaultValue)

	if strings.HasPrefix(trimmedVal, "\"") && strings.HasSuffix(trimmedVal, "\"") {
		return STRING
	}

	if defaultValue == "0" || defaultValue == "1" {
		return LOGIC
	}

	if strings.Contains(trimmedVal, "'") { // A single quote is a strong indicator
		lowerVal := strings.ToLower(trimmedVal)
		if strings.Contains(lowerVal, "'b") {
			return BIT // Or LOGIC. BIT is common for such defaults.
		}
		if strings.Contains(lowerVal, "'h") {
			return LOGIC // General type for hex values. Could be BYTE, INT etc., but LOGIC is safe.
		}
		if strings.Contains(lowerVal, "'o") {
			return LOGIC // General type for octal values.
		}
		// Check for explicit decimal base like 16'd100 or 'd10
		if strings.Contains(lowerVal, "'d") {
			return INTEGER // Or INT. INTEGER is a good general type.
		}
		// SystemVerilog unsized single-bit literals '0, '1, 'z, 'x
		if trimmedVal == "'0" || trimmedVal == "'1" || lowerVal == "'x" || lowerVal == "'z" {
			return BIT
		}
	}

	timeSuffixes := []string{"fs", "ps", "ns", "us", "ms", "s"}
	for _, suffix := range timeSuffixes {
		if strings.HasSuffix(trimmedVal, suffix) {
			numericPart := strings.TrimSuffix(trimmedVal, suffix)
			if _, err := strconv.ParseFloat(numericPart, 64); err == nil {
				return TIME
			}
			if _, err := strconv.ParseInt(numericPart, 10, 64); err == nil {
				return TIME
			}
		}
	}

	if strings.Contains(trimmedVal, ".") {
		if _, err := strconv.ParseFloat(trimmedVal, 64); err == nil {
			return REAL
		}
	}

	if _, err := strconv.ParseInt(trimmedVal, 10, 64); err == nil {
		return INTEGER
	}

	if strings.HasPrefix(trimmedVal, "0x") || strings.HasPrefix(trimmedVal, "0X") {
		if _, err := strconv.ParseInt(trimmedVal, 0, 64); err == nil {
			return LOGIC // Or INTEGER. LOGIC is a safe bet if width is unknown.
		}
	}

	return UNKNOWN
}

// splitParametersSmart splits a parameter list string by commas while respecting
// nested structures (parentheses, brackets, braces) to avoid splitting inside
// complex expressions like ternary operators, function calls, etc.
func splitParametersSmart(parameterListString string) []string {
	if strings.TrimSpace(parameterListString) == "" {
		return []string{}
	}

	var result []string
	var current strings.Builder
	var parenDepth, bracketDepth, braceDepth int
	var inString bool

	for i, r := range parameterListString {
		switch r {
		case '"':
			// Only double quotes start/end string literals in Verilog
			if !inString {
				inString = true
			} else if i > 0 && parameterListString[i-1] != '\\' {
				inString = false
			}
		case '(':
			if !inString {
				parenDepth++
			}
		case ')':
			if !inString {
				parenDepth--
			}
		case '[':
			if !inString {
				bracketDepth++
			}
		case ']':
			if !inString {
				bracketDepth--
			}
		case '{':
			if !inString {
				braceDepth++
			}
		case '}':
			if !inString {
				braceDepth--
			}
		case ',':
			// Only split on comma if we're not inside any nested structure
			if !inString && parenDepth == 0 && bracketDepth == 0 && braceDepth == 0 {
				result = append(result, current.String())
				current.Reset()
				continue
			}
		}
		current.WriteRune(r)
	}

	// Add the last parameter
	if current.Len() > 0 {
		result = append(result, current.String())
	}

	return result
}

func parseParameters(parameterListString string, ansiStyle bool) ([]*Parameter, error) {
	params := splitParametersSmart(parameterListString)
	parametersList := []*Parameter{}

	for _, paramStr := range params {
		trimmedParamStr := strings.TrimSpace(paramStr)
		if trimmedParamStr == "" {
			continue
		}

		matches := matchAllParametersFromString(trimmedParamStr)

		if len(matches) == 7 {
			paramLocalityStr := strings.TrimSpace(matches[1])
			paramTypeStr := strings.TrimSpace(matches[2])
			paramWidthStr := strings.TrimSpace(matches[3])
			paramWidth, err := parseRange(paramWidthStr, nil)
			if err != nil {
				logger.Warn(
					"Could not parse range '%s' for parameter '%s'. Using default width %d. Error: %v",
					paramWidthStr,
					trimmedParamStr,
					paramWidth, // Use the width returned by parseRange (the default)
					err,
				)
			}
			paramName := strings.TrimSpace(matches[4])
			paramValue := ""
			if matches[5] == "=" {
				paramValue = strings.TrimSpace(matches[6])
			}

			if paramName == "" {
				logger.Warn(
					"could not parse parameter fragment, missing parameter name in: '%s'",
					trimmedParamStr,
				)
				continue
			}
			paramType := getType(paramTypeStr)
			paramLocality := paramLocalityStr == "localparam"

			if paramTypeStr == "" && paramLocalityStr == "" && paramValue == "" {
				// Parameter defined in an enum of params separated by commas
				if len(parametersList) > 0 {
					paramType = parametersList[len(parametersList)-1].Type
					paramLocality = parametersList[len(parametersList)-1].Localparam
				}
			}

			if paramName == "parameter" || paramName == "localparam" ||
				baseTypesRegex.MatchString(paramName) {
				logger.Warn(
					"Missing name in parameter fragment: '%s'. Skipping.",
					trimmedParamStr,
				)
				continue
			}

			if paramTypeStr == "" && paramValue != "" {
				paramType = inferTypeFromDefaultValue(paramValue)
				if paramType == UNKNOWN {
					logger.Debug(
						"Could not infer type from default value '%s' for parameter '%s'",
						paramValue,
						paramName,
					)
				}
			}

			parametersList = append(parametersList, &Parameter{
				Name:         paramName,
				Type:         paramType,
				DefaultValue: paramValue,
				Localparam:   paramLocality,
				Width:        paramWidth,
				AnsiStyle:    ansiStyle,
			})
		} else {
			logger.Warn(
				"could not parse parameter fragment: '%s'",
				trimmedParamStr,
			)
			continue
		}
	}
	return parametersList, nil
}

func parsePortsAndUpdateModule(portList string, module *Module) error {
	paramMap := parametersToMap(module.Parameters)

	headerPorts, _ := extractANSIPortDeclarations(
		portList,
		paramMap,
	) // headerPortOrder is no longer used by mergePortInfo directly
	parsedPortsMap, scanErr := extractNonANSIPortDeclarations(
		module.Body,
		paramMap,
	)
	if scanErr != nil {
		logger.Warn("Error during scan for non-ANSI ports: %v", scanErr)
		if parsedPortsMap == nil {
			parsedPortsMap = make(map[string]*Port)
		}
	}

	module.AnsiStyle = len(parsedPortsMap) == 0

	// Merge header and body scan information
	module.Ports = mergePortInfo(headerPorts, parsedPortsMap)

	// Apply fallback for ports that remained placeholders after merge
	// For now, it iterates over headerPorts which might be sufficient if placeholders are primarily from there.
	applyPortDeclarationFallback(
		module,
		headerPorts, // Still pass headerPorts for fallback logic to check against original header list
		parsedPortsMap,
	)

	if len(module.Ports) == 0 && portList != "" {
		return fmt.Errorf(
			"failed to parse any ports for module %s despite port list being present",
			module.Name,
		)
	} else if len(module.Ports) == 0 {
		logger.Warn("No ports found or parsed for module %s. Module might have no ports.", module.Name)
	}
	return nil
}

// isLikelyOutputPort uses heuristics to determine if a port name suggests it's an output port
func isLikelyOutputPort(portName string) bool {
	portNameLower := strings.ToLower(portName)

	// Common output port prefixes and patterns
	outputPatterns := []string{
		"out", "output", "result", "resp", "data_out", "valid_out",
		"ready_out", "done", "complete", "status", "flag",
	}

	// Common input port prefixes and patterns
	inputPatterns := []string{
		"in", "input", "clk", "clock", "rst", "reset", "enable", "en",
		"data_in", "valid_in", "ready_in", "req", "cmd", "addr", "address",
	}

	// Check for explicit input patterns first (these take precedence)
	for _, pattern := range inputPatterns {
		if strings.Contains(portNameLower, pattern) {
			return false
		}
	}

	// Check for output patterns
	for _, pattern := range outputPatterns {
		if strings.Contains(portNameLower, pattern) {
			return true
		}
	}

	// If no clear pattern, be conservative and assume it could be an output
	// This can be refined based on additional heuristics or module definitions
	return true
}

// getModulePortDirection gets the actual port direction from the module definition
// Returns the PortDirection and true if found, or INPUT and false if not found
func getModulePortDirection(
	vf *VerilogFile,
	moduleName string,
	portName string,
) (PortDirection, bool) {
	if vf == nil || vf.Modules == nil {
		return INPUT, false
	}

	module, exists := vf.Modules[moduleName]
	if !exists {
		return INPUT, false
	}

	for _, port := range module.Ports {
		if port.Name == portName {
			return port.Direction, true
		}
	}

	return INPUT, false
}

// isValidVariableName checks if a string is a valid variable name and not a literal or constant
func isValidVariableName(name string) bool {
	// Skip empty names
	if name == "" {
		return false
	}

	// Skip constants and literals
	if strings.HasPrefix(name, "'") || // Verilog literals like 'h, 'b
		strings.Contains(name, "'h") || strings.Contains(name, "'b") ||
		strings.Contains(name, "'d") || strings.Contains(name, "'o") {
		return false
	}

	// Skip numeric literals
	if len(name) > 0 && (name[0] >= '0' && name[0] <= '9') {
		return false
	}

	// Skip expressions (containing operators)
	if strings.ContainsAny(name, "+-*/&|^~<>=!()[]{}") {
		return false
	}

	// Must start with letter or underscore and contain only alphanumeric and underscore
	if len(name) > 0 && (name[0] == '_' ||
		(name[0] >= 'a' && name[0] <= 'z') ||
		(name[0] >= 'A' && name[0] <= 'Z')) {
		for _, char := range name {
			if (char < 'a' || char > 'z') && (char < 'A' || char > 'Z') &&
				(char < '0' || char > '9') &&
				char != '_' {
				return false
			}
		}
		return true
	}

	return false
}

// detectBlockedVariables analyzes the content to find variables that are assigned
// in blocking constructs and should not be reused in parent scopes
func detectBlockedVariables(vf *VerilogFile, content string) map[string]bool {
	blockedVars := make(map[string]bool)

	// Detect variables blocked by different types of assignments
	detectContinuousAssignments(content, blockedVars)
	detectWireAssignments(content, blockedVars)
	detectForceStatements(content, blockedVars)
	detectAlwaysBlockAssignments(content, blockedVars)
	detectModuleInstantiationOutputs(vf, content, blockedVars)

	return blockedVars
}

// detectContinuousAssignments finds variables assigned in continuous assignments (assign statements)
func detectContinuousAssignments(content string, blockedVars map[string]bool) {
	assignMatches := assignRegex.FindAllStringSubmatch(content, -1)
	for _, match := range assignMatches {
		if len(match) >= 2 {
			varName := strings.TrimSpace(match[1])
			if varName != "" {
				blockedVars[varName] = true
			}
		}
	}
}

// detectWireAssignments finds variables assigned in wire assignments
func detectWireAssignments(content string, blockedVars map[string]bool) {
	wireAssignMatches := wireAssignRegex.FindAllStringSubmatch(content, -1)
	for _, match := range wireAssignMatches {
		if len(match) >= 2 {
			varName := strings.TrimSpace(match[1])
			if varName != "" {
				blockedVars[varName] = true
			}
		}
	}
}

// detectForceStatements finds variables assigned in force statements
func detectForceStatements(content string, blockedVars map[string]bool) {
	forceMatches := forceRegex.FindAllStringSubmatch(content, -1)
	for _, match := range forceMatches {
		if len(match) >= 2 {
			varName := strings.TrimSpace(match[1])
			if varName != "" {
				blockedVars[varName] = true
			}
		}
	}
}

// detectAlwaysBlockAssignments finds variables assigned in always blocks (always_comb, always_ff, always @)
func detectAlwaysBlockAssignments(content string, blockedVars map[string]bool) {
	detectAlwaysCombAssignments(content, blockedVars)
	detectAlwaysFFAssignments(content, blockedVars)
	detectGeneralAlwaysAssignments(content, blockedVars)
}

// detectAlwaysCombAssignments finds variables assigned in always_comb blocks
func detectAlwaysCombAssignments(content string, blockedVars map[string]bool) {
	alwaysCombMatches := alwaysCombRegex.FindAllStringSubmatch(content, -1)
	for _, match := range alwaysCombMatches {
		if len(match) >= 2 {
			blockContent := match[1]
			extractAssignmentsFromBlock(blockContent, blockedVars)
		}
	}
}

// detectAlwaysFFAssignments finds variables assigned in always_ff blocks
func detectAlwaysFFAssignments(content string, blockedVars map[string]bool) {
	alwaysFFMatches := alwaysFFRegex.FindAllStringSubmatch(content, -1)
	for _, match := range alwaysFFMatches {
		if len(match) >= 2 {
			blockContent := match[1]
			extractAssignmentsFromBlock(blockContent, blockedVars)
		}
	}
}

// detectGeneralAlwaysAssignments finds variables assigned in general always blocks (always @)
func detectGeneralAlwaysAssignments(content string, blockedVars map[string]bool) {
	alwaysMatches := alwaysRegex.FindAllStringSubmatch(content, -1)
	for _, match := range alwaysMatches {
		if len(match) >= 2 {
			blockContent := match[1]
			extractAssignmentsFromBlock(blockContent, blockedVars)
		}
	}
}

// extractAssignmentsFromBlock extracts variable assignments from a block of code
func extractAssignmentsFromBlock(blockContent string, blockedVars map[string]bool) {
	assignMatches := blockingAssignRegex.FindAllStringSubmatch(blockContent, -1)
	for _, assignMatch := range assignMatches {
		if len(assignMatch) >= 2 {
			varName := strings.TrimSpace(assignMatch[1])
			if varName != "" {
				blockedVars[varName] = true
			}
		}
	}
}

// detectModuleInstantiationOutputs finds variables assigned through module instantiation output/inout ports
func detectModuleInstantiationOutputs(
	vf *VerilogFile,
	content string,
	blockedVars map[string]bool,
) {
	moduleInstMatches := moduleInstRegex.FindAllStringSubmatch(content, -1)
	for _, match := range moduleInstMatches {
		if len(match) >= 4 {
			moduleName := strings.TrimSpace(match[1])
			portConnections := match[3]
			processModulePortConnections(vf, moduleName, portConnections, blockedVars)
		}
	}
}

// processModulePortConnections processes port connections for a module instantiation
func processModulePortConnections(
	vf *VerilogFile,
	moduleName string,
	portConnections string,
	blockedVars map[string]bool,
) {
	portMatches := portConnectionRegex.FindAllStringSubmatch(portConnections, -1)
	for _, portMatch := range portMatches {
		if len(portMatch) >= 3 {
			portName := strings.TrimSpace(portMatch[1])
			connectedVar := strings.TrimSpace(portMatch[2])

			// Skip if connected to constants, literals, or expressions
			if connectedVar != "" && isValidVariableName(connectedVar) {
				determinePortBlockingStatus(vf, moduleName, portName, connectedVar, blockedVars)
			}
		}
	}
}

// determinePortBlockingStatus determines if a variable should be blocked based on port direction
func determinePortBlockingStatus(
	vf *VerilogFile,
	moduleName string,
	portName string,
	connectedVar string,
	blockedVars map[string]bool,
) {
	// Use actual port direction from module definition
	if vf == nil {
		blockedVars[connectedVar] = false
		return
	}

	if direction, found := getModulePortDirection(vf, moduleName, portName); found {
		// Block variables connected to output or inout ports
		if direction == OUTPUT || direction == INOUT {
			blockedVars[connectedVar] = true
		}
	} else {
		// If we can't find the module definition, use heuristics as fallback
		if isLikelyOutputPort(portName) {
			blockedVars[connectedVar] = true
		}
		logger.Warn(
			"Could not determine port direction for '%s' in module '%s'. Assuming %v.",
			portName,
			moduleName,
			blockedVars[connectedVar],
		)
	}
}

// MarkVariableAsBlocked marks a variable as blocked (used as output) in the scope tree
func MarkVariableAsBlockedInChildren(scopeNode *ScopeNode, varName string) {
	// Search through all scope nodes to find and mark the variable as blocked
	var markInNode func(*ScopeNode)
	markInNode = func(node *ScopeNode) {
		if scopeVar, exists := node.Variables[varName]; exists {
			scopeVar.Blocked = true
		}
		for _, child := range node.Children {
			markInNode(child)
		}
	}
	markInNode(scopeNode)
}

func MarkVariableAsBlockedInParents(scopeNode *ScopeNode, varName string) {
	if scopeNode == nil {
		return
	}
	// Mark the variable as blocked in the current scope node
	if scopeVar, exists := scopeNode.Variables[varName]; exists {
		scopeVar.Blocked = true
	}
	// Recursively mark the variable as blocked in all parent scope nodes
	if scopeNode.Parent != nil {
		MarkVariableAsBlockedInParents(scopeNode.Parent, varName)
	}
}

func MarkVariableAsBlocked(scopeNode *ScopeNode, varName string) {
	// Mark the variable as blocked in the current scope node
	if scopeVar, exists := scopeNode.Variables[varName]; exists {
		scopeVar.Blocked = true
	}
	// Recursively mark the variable as blocked in all parent scope nodes
	if scopeNode.Parent != nil {
		MarkVariableAsBlockedInParents(scopeNode.Parent, varName)
	}

	// Also mark the variable as blocked in all child scope nodes
	for _, child := range scopeNode.Children {
		if scopeVar, exists := child.Variables[varName]; exists {
			scopeVar.Blocked = true
		}
		// Recursively mark in children
		MarkVariableAsBlocked(child, varName)
	}
}

// GetAvailableVariablesForOutput returns variables that can be used as outputs (not blocked)
func GetAvailableVariablesForOutput(node *ScopeNode) map[string]*ScopeVariable {
	available := make(map[string]*ScopeVariable)
	curr := node
	for curr != nil {
		for name, scopeVar := range curr.Variables {
			if !scopeVar.Blocked {
				available[name] = scopeVar
			}
		}
		curr = curr.Parent
	}
	return available
}

// GetAvailableVariablesForInput returns all variables that can be used as inputs (including blocked ones)
func GetAvailableVariablesForInput(node *ScopeNode) map[string]*ScopeVariable {
	available := make(map[string]*ScopeVariable)
	curr := node
	for curr != nil {
		for name, scopeVar := range curr.Variables {
			available[name] = scopeVar
		}
		curr = curr.Parent
	}
	return available
}

// removeBlockedVariablesFromParents removes blocked variables from parent scope nodes
func removeBlockedVariablesFromParents(scopeNode *ScopeNode, blockedVars map[string]bool) {
	if scopeNode == nil {
		return
	}

	// Process all children first (bottom-up approach)
	for _, child := range scopeNode.Children {
		removeBlockedVariablesFromParents(child, blockedVars)
	}

	// Remove blocked variables from current scope if they exist in parent scopes
	for varName := range blockedVars {
		if _, exists := scopeNode.Variables[varName]; exists {
			// Check if this variable is assigned in a blocking way in any child scope
			if isVariableBlockedInChildren(scopeNode, varName, blockedVars) {
				delete(scopeNode.Variables, varName)
			}
		}
	}
}

// isVariableBlockedInChildren checks if a variable is blocked in any child scope
func isVariableBlockedInChildren(
	scopeNode *ScopeNode,
	varName string,
	blockedVars map[string]bool,
) bool {
	// If the variable is globally blocked, return true
	if blockedVars[varName] {
		return true
	}

	// Check if any child scope has this variable blocked
	for _, child := range scopeNode.Children {
		if isVariableBlockedInChildren(child, varName, blockedVars) {
			return true
		}
	}

	return false
}

func ParseVariables(v *VerilogFile,
	content string,
	scopeParams []*Parameter,
) (map[string]*Variable, error) {
	variables, _, err := parseVariablesWithScope(v, content, scopeParams, nil, true)
	return variables, err
}

func GetScopeTree(v *VerilogFile,
	content string,
	scopeParams []*Parameter,
	modulePorts []*Port,
) (*ScopeNode, error) {
	_, scopeTree, err := parseVariablesWithScope(v, content, scopeParams, modulePorts, false)
	if err != nil {
		return nil, err
	}
	return scopeTree, nil
}

var excludedScopeRegex = regexp.MustCompile(`^\s*(?:typedef)\b`)

// parseVariablesWithScope parses variables from the provided content and organizes them into a scope tree.
// It returns a map of variable names to Variable objects, the root ScopeNode, and any error encountered.
// The scopeParams are used to resolve parameter ranges, and modulePorts are ONLY used for the scope Tree
func parseVariablesWithScope(v *VerilogFile,
	content string,
	scopeParams []*Parameter,
	modulePorts []*Port,
	skipScopeTree bool,
) (map[string]*Variable, *ScopeNode, error) {
	scopeParamsMap := parametersToMap(scopeParams)
	variablesMap := make(map[string]*Variable)
	scopeTree := &ScopeNode{
		Level:     0,
		Variables: make(map[string]*ScopeVariable),
		Children:  []*ScopeNode{},
		Parent:    nil,
		LastLine:  -1,
	}
	scopeNode := scopeTree

	// Process content line by line to track line numbers
	lines := strings.Split(content, "\n")
	isExcludedScope := false
	excludedLevel := -1
	for lineNumber, line := range lines {
		// Try to match variable declarations on this line
		matchedVariable := generalVariableRegex.FindStringSubmatch(line)
		if len(matchedVariable) < 6 {
			if strings.TrimSpace(line) == "" || skipScopeTree {
				continue
			}
			line = strings.ReplaceAll(line, "\t", "    ")
			indentation := (len(line) - len(strings.TrimLeft(line, " "))) / 4
			if excludedScopeRegex.MatchString(line) {
				isExcludedScope = true
				excludedLevel = indentation
			}
			if indentation == scopeNode.Level {
				scopeNode.LastLine = lineNumber // choice to be done on only using the variable last lines or all the scope's lines
			} else {
				for scopeNode.Level > indentation {
					scopeNode = scopeNode.Parent
					scopeNode.LastLine = lineNumber // Not used for the moment but might come in handy later
				}
				if isExcludedScope && excludedLevel > indentation {
					// we exited the excluded scope
					isExcludedScope = false
					excludedLevel = -1
				}
				if !isExcludedScope && !skipScopeTree {
					newScopeNode := &ScopeNode{
						Level:     indentation,
						Variables: make(map[string]*ScopeVariable),
						Children:  []*ScopeNode{},
						Parent:    scopeNode,
						LastLine:  lineNumber,
					}
					scopeNode.Children = append(scopeNode.Children, newScopeNode)
					scopeNode = newScopeNode
				}
			}
			continue // No variable declaration on this line
		}

		line = strings.ReplaceAll(line, "\t", "    ")
		indent := (len(line) - len(strings.TrimLeft(line, " "))) / 4
		varType := getType(matchedVariable[2])
		widthStr := matchedVariable[3]
		width, err := parseRange(widthStr, scopeParamsMap)
		if err != nil {
			if width != 0 {
				logger.Warn(
					"Could not parse range '%s' for variable '%s'. Using default width %d. Error: %v",
					widthStr,
					matchedVariable[4],
					width,
					err,
				)
			} else {
				return nil, nil, fmt.Errorf("failed to parse width: %v", err)
			}
		}

		var parentStruct *Struct
		var parentClass *Class
		if varType == UNKNOWN && v != nil {
			// Check if it's a struct or class that we have already defined
			if _, exists := v.Structs[matchedVariable[2]]; exists {
				varType = USERDEFINED
				parentStruct = v.Structs[matchedVariable[2]]
			} else if _, exists := v.Classes[matchedVariable[2]]; exists {
				varType = USERDEFINED
				parentClass = v.Classes[matchedVariable[2]]
			} else {
				return nil, nil, fmt.Errorf("unknown type '%s' for variable '%s'", matchedVariable[2], matchedVariable[5])
			}
		}
		unsigned := matchedVariable[4] == "unsigned"
		for _, decl := range strings.Split(matchedVariable[5], ",") {
			decl = strings.TrimSpace(decl)
			if decl == "" {
				continue
			}
			arrayMatch := matchArraysFromString(decl)
			if len(arrayMatch) != 3 {
				logger.Warn(
					"could not parse variable fragment, missing variable name in: '%s'",
					decl,
				)
				continue
			}
			varName := strings.TrimSpace(arrayMatch[1])
			if varName == "" {
				logger.Warn(
					"could not parse variable fragment, missing variable name in: '%s'",
					decl,
				)
				continue
			}

			variable := &Variable{
				Name:         varName,
				Type:         varType,
				Width:        width,
				Unsigned:     unsigned,
				ParentStruct: parentStruct,
				ParentClass:  parentClass,
				Array:        arrayMatch[2],
			}
			variablesMap[varName] = variable

			if !isExcludedScope && !skipScopeTree {
				// Create ScopeVariable wrapper for scope tracking
				scopeVariable := &ScopeVariable{
					Variable: variable,
					Blocked:  false, // Initially not blocked
				}

				if indent == scopeNode.Level {
					scopeNode.Variables[variable.Name] = scopeVariable
					scopeNode.LastLine = lineNumber
				} else {
					for scopeNode.Level > indent {
						scopeNode = scopeNode.Parent
					}
					newScopeNode := &ScopeNode{
						Level:     indent,
						Variables: make(map[string]*ScopeVariable),
						Children:  []*ScopeNode{},
						Parent:    scopeNode,
					}
					newScopeNode.Variables[variable.Name] = scopeVariable
					newScopeNode.LastLine = lineNumber
					scopeNode.Children = append(scopeNode.Children, newScopeNode)
					scopeNode = newScopeNode
				}
			}
		}
	}
	if !skipScopeTree {
		// Add all module ports to the root of the scope tree
		addPortsToScopeTree(modulePorts, scopeTree)

		// After parsing all variable declarations, detect blocked variables and remove them from parent scopes
		blockedVars := detectBlockedVariables(v, content)
		for blockedVar := range blockedVars {
			MarkVariableAsBlockedInChildren(scopeTree, blockedVar)
		}
		// removeBlockedVariablesFromParents(scopeTree, blockedVars)

		// Remove task/class variables from scope tree (but keep them in variablesMap)
		taskClassVars := detectTaskClassScopeVariables(content)
		removeTaskClassVariablesFromScopes(scopeTree, taskClassVars)
	}

	return variablesMap, scopeTree, nil
}

func addPortsToScopeTree(modulePorts []*Port, scopeTree *ScopeNode) {
	for _, port := range modulePorts {
		if port.Name == "" {
			logger.Warn("Skipping module port with empty name")
			continue
		}
		// Be careful for non ANSI ports they are parsed as variables and are in the scope of level 1
		MarkVariableAsBlockedInParents(scopeTree, port.Name)
		MarkVariableAsBlockedInChildren(scopeTree, port.Name)
		if _, exists := scopeTree.Variables[port.Name]; !exists {
			if _, exists := scopeTree.Children[0].Variables[port.Name]; !exists {
				// for NON ANSI ports to be sure they do not exist
				if port.Direction == INPUT {
					variable := &Variable{
						Name:     port.Name,
						Type:     port.Type,
						Width:    port.Width,
						Unsigned: !port.IsSigned,
						Array:    port.Array,
					}
					// Create ScopeVariable wrapper for module ports
					scopeVariable := &ScopeVariable{
						Variable: variable,
						Blocked:  true, // Module input ports start blocked
					}
					scopeTree.Variables[port.Name] = scopeVariable
				}
			} else {
				// move it from the child to the root
				scopeTree.Variables[port.Name] = scopeTree.Children[0].Variables[port.Name]
				delete(scopeTree.Children[0].Variables, port.Name)
			}
		}
	}
}

func (v *VerilogFile) parseStructs(
	content string,
	firstPass bool,
) error {
	if firstPass {
		v.Structs = make(map[string]*Struct)
	}
	allMatchedStructs := matchAllStructsFromString(content)
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
			variablesMap, err := ParseVariables(v, varList, nil) // TODO: check that we don't have params that need to be sent as args here
			if err != nil {
				return fmt.Errorf("failed to parse variables in struct '%s': %v", structName, err)
			}
			variables := []*Variable{}
			for _, variable := range variablesMap {
				variables = append(variables, variable)
			}
			v.Structs[structName].Variables = variables
			for _, variable := range variables {
				if variable.Type == USERDEFINED {
					if variable.ParentStruct != nil {
						v.AddDependency(structName, variable.ParentStruct.Name)
					}
					if variable.ParentClass != nil {
						v.AddDependency(structName, variable.ParentClass.Name)
					}
				}
			}
		}
	}
	return nil
}

func (v *VerilogFile) parseTypedefs(content string) error {
	v.Typedefs = make(map[string]*Typedef)
	matches := matchAllTypedefsFromString(content)
	for _, match := range matches {
		if len(match) > 2 {
			typedef := &Typedef{
				Name:    strings.TrimSpace(match[2]),
				Content: strings.TrimSpace(match[0]),
			}
			if typedef.Name == "" {
				continue
			}
			v.Typedefs[typedef.Name] = typedef
		}
	}
	return nil
}

// parseModPort parses a single modport declaration and returns the ModPort struct
// This is primarily used for testing individual modport parsing
// parseInterfacePorts parses interface port declarations (input/output ports of the interface itself)
func parseInterfacePorts(
	portListStr string,
	parameters map[string]*Parameter,
) ([]*InterfacePort, error) {
	ports := []*InterfacePort{}

	if strings.TrimSpace(portListStr) == "" {
		return ports, nil
	}

	// Split by comma and parse each port
	portDecls := strings.Split(portListStr, ",")
	for _, portDecl := range portDecls {
		portDecl = strings.TrimSpace(portDecl)
		if portDecl == "" {
			continue
		}

		// Use similar regex as ANSI port parsing
		matches := ansiPortRegex.FindStringSubmatch(portDecl)
		if len(matches) != 7 {
			pragma := strings.TrimSpace(matches[1])
			directionStr := strings.TrimSpace(matches[2])
			portTypeStr := strings.TrimSpace(matches[3])
			signedStr := strings.TrimSpace(matches[4])
			rangeStr := strings.TrimSpace(matches[5])
			portName := strings.TrimSpace(matches[6])

			direction := getPortDirection(directionStr)
			portType := getType(portTypeStr)
			isSigned := (signedStr == "signed")

			width, err := parseRange(rangeStr, parameters)
			if err != nil {
				// For interface ports, width should be 0 when no explicit range is specified
				width = 0
			}

			port := InterfacePort{
				Name:      portName,
				Direction: direction,
				Type:      portType,
				Width:     width,
				IsSigned:  isSigned,
				Pragma:    pragma,
			}

			ports = append(ports, &port)
		}
	}

	return ports, nil
}

// parseModPortsFromBody extracts modport declarations from interface body
func parseModPortsFromBody(bodyStr string) ([]*ModPort, error) {
	modports := []*ModPort{}

	// Regex to find all modport declarations in the body
	matches := ModportRegex.FindAllStringSubmatch(bodyStr, -1)

	for _, match := range matches {
		if len(match) < 3 {
			continue
		}

		modportName := match[1]
		signalsList := match[2]

		modport := ModPort{
			Name:    modportName,
			Signals: []*ModPortSignal{},
		}

		// Parse signals within the modport
		if strings.TrimSpace(signalsList) != "" {
			signals, err := parseModPortSignals(signalsList)
			if err != nil {
				logger.Warn("Failed to parse signals for modport '%s': %v", modportName, err)
			} else {
				modport.Signals = signals
			}
		}

		modports = append(modports, &modport)
	}

	return modports, nil
}

// parseModPortSignals parses signal declarations within a modport
func parseModPortSignals(signalsList string) ([]*ModPortSignal, error) {
	signals := []*ModPortSignal{}

	// Clean up the signals list and split by comma to handle individual declarations
	signalsList = strings.ReplaceAll(signalsList, "\n", " ")
	signalsList = strings.ReplaceAll(signalsList, "\t", " ")

	// Split by comma first to get individual signal declarations
	parts := strings.Split(signalsList, ",")

	currentDirection := INTERNAL // Track the current direction for signal lists

	for _, part := range parts {
		part = strings.TrimSpace(part)
		if part == "" {
			continue
		}

		// Match direction and signal name: "input signal_name" or "output signal_name"
		signalRegex := regexp.MustCompile(`^\s*(input|output|inout)\s+(\w+)\s*$`)
		signalMatches := signalRegex.FindStringSubmatch(part)

		if len(signalMatches) >= 3 {
			// Found a part with explicit direction
			currentDirection = getPortDirection(signalMatches[1])
			signalName := strings.TrimSpace(signalMatches[2])

			if signalName != "" {
				signals = append(signals, &ModPortSignal{
					Name:      signalName,
					Direction: currentDirection,
				})
			}
		} else {
			// Check if this is just a signal name without direction (reuses previous direction)
			signalNameRegex := regexp.MustCompile(`^\s*(\w+)\s*$`)
			nameMatches := signalNameRegex.FindStringSubmatch(part)

			if len(nameMatches) >= 2 && currentDirection != INTERNAL {
				signalName := strings.TrimSpace(nameMatches[1])
				if signalName != "" {
					signals = append(signals, &ModPortSignal{
						Name:      signalName,
						Direction: currentDirection,
					})
				}
			}
		}
	}

	return signals, nil
}

func (v *VerilogFile) parseInterfaces(
	content string,
) error {
	allMatchedInterfaces := matchAllInterfacesFromString(content)
	v.Interfaces = make(map[string]*Interface)

	for _, matchedInterface := range allMatchedInterfaces {
		if len(matchedInterface) < 7 {
			return errors.New("no interface found in the provided text")
		}

		virtualStr := matchedInterface[1]    // "virtual" or empty
		interfaceName := matchedInterface[2] // interface name
		paramListStr := matchedInterface[3]  // parameter list
		extendsFrom := matchedInterface[4]   // extends interface name
		portListStr := matchedInterface[5]   // port list
		bodyStr := matchedInterface[6]       // interface body

		i := &Interface{
			Name:        interfaceName,
			IsVirtual:   virtualStr == "virtual",
			ExtendsFrom: extendsFrom,
			Body:        bodyStr,
			Ports:       []*InterfacePort{},
			Parameters:  []*Parameter{},
			ModPorts:    []*ModPort{},
			Variables:   []*Variable{},
		}

		// Parse parameters if present
		if paramListStr != "" {
			params, err := parseParameters(paramListStr, false)
			if err != nil {
				logger.Warn("Failed to parse interface parameters for '%s': %v", interfaceName, err)
			} else {
				i.Parameters = params
			}
		}

		// Parse interface ports if present
		if portListStr != "" {
			ports, err := parseInterfacePorts(portListStr, parametersToMap(i.Parameters))
			if err != nil {
				logger.Warn("Failed to parse interface ports for '%s': %v", interfaceName, err)
			} else {
				i.Ports = ports
			}
		}

		// Parse variables from body
		if bodyStr != "" {
			variablesMap, err := ParseVariables(v, bodyStr, i.Parameters)
			if err != nil {
				logger.Warn("Failed to parse variables in interface '%s': %v", interfaceName, err)
			} else {
				variables := []*Variable{}
				for _, variable := range variablesMap {
					variables = append(variables, variable)
				}
				i.Variables = variables
			}

			// Parse modports from body
			modports, err := parseModPortsFromBody(bodyStr)
			if err != nil {
				logger.Warn("Failed to parse modports in interface '%s': %v", interfaceName, err)
			} else {
				i.ModPorts = modports
			}
		}

		v.Interfaces[interfaceName] = i
	}
	return nil
}

func (v *VerilogFile) parsePackages(content string) error {
	allMatchedPackages := matchAllPackagesFromString(content)
	v.Packages = make(map[string]*Package)

	for _, matchedPackage := range allMatchedPackages {
		if len(matchedPackage) < 3 {
			return errors.New("no package found in the provided text")
		}

		packageName := matchedPackage[1] // package name
		bodyStr := matchedPackage[2]     // package body

		pkg := &Package{
			Name:       packageName,
			Body:       bodyStr,
			Typedefs:   []string{},
			Imports:    []string{},
			Variables:  []*Variable{},
			Parameters: []*Parameter{},
		}

		// Parse typedef statements - handle multi-line typedefs like enums and structs
		typedefMatches := typedefRegex.FindAllString(bodyStr, -1)
		for _, typedefMatch := range typedefMatches {
			pkg.Typedefs = append(pkg.Typedefs, strings.TrimSpace(typedefMatch))
		}

		// Parse import statements
		importMatches := importRegex.FindAllString(bodyStr, -1)
		for _, importMatch := range importMatches {
			pkg.Imports = append(pkg.Imports, strings.TrimSpace(importMatch))
		}

		// Parse variables from body
		if bodyStr != "" {
			variablesMap, err := ParseVariables(v, bodyStr, pkg.Parameters)
			if err != nil {
				logger.Warn("Failed to parse variables in package '%s': %v", packageName, err)
			} else {
				variables := []*Variable{}
				for _, variable := range variablesMap {
					variables = append(variables, variable)
				}
				pkg.Variables = variables
			}

			// Parse parameters/localparams from body
			bodyParameters, err := extractNonANSIParameterDeclarations(bodyStr)
			if err != nil {
				logger.Warn("Failed to parse parameters in package '%s': %v", packageName, err)
			} else {
				pkg.Parameters = bodyParameters
			}
		}

		v.Packages[packageName] = pkg
	}
	return nil
}

// Only parses the dependencies of the classes
// Probably overengineered and should only see if the name of a class or a struct just happens to be there but too late I already wrote it
func (v *VerilogFile) typeDependenciesParser() error {
	for _, class := range v.Classes {
		if class.extends != "" {
			v.AddDependency(
				class.Name,
				class.extends,
			)
		}
		if v.Typedefs[class.Name] != nil {
			v.AddDependency(
				class.Name,
				v.Typedefs[class.Name].Name,
			)
		}
		vars := matchUserDefinedVariablesFromString(v, class.Body)
		for _, matchedVariable := range vars {
			if len(matchedVariable) < 4 {
				return errors.New("no variable found in the provided text")
			}
			userTypeStr := matchedVariable[2]
			v.AddDependency(
				class.Name,
				userTypeStr,
			)
		}
	}
	for _, module := range v.Modules {
		// Check for interface dependencies in module ports
		for _, port := range module.Ports {
			if port.IsInterfacePort() {
				// Add dependency on the interface
				v.AddDependency(
					module.Name,
					port.InterfaceName,
				)
			}
		}

		// Check for interface instantiations in module body
		interfaceInstantiations := matchInterfaceInstantiationsFromString(v, module.Body)
		v.AddDependency(module.Name, interfaceInstantiations...)

		// Check for module instantiations in module body
		moduleInstantiations := matchModuleInstantiationsFromString(v, module.Body)
		v.AddDependency(module.Name, moduleInstantiations...)

		// Check for package imports in module body
		packageImports := matchPackageImportsFromString(v, module.Body)
		v.AddDependency(module.Name, packageImports...)

		// Check for class instantiations in module body
		classInstantiations := matchClassInstantiationsFromString(v, module.Body)
		v.AddDependency(module.Name, classInstantiations...)

		// Check for user-defined type dependencies in module body
		vars := matchUserDefinedVariablesFromString(v, module.Body)
		for _, matchedVariable := range vars {
			if len(matchedVariable) < 4 {
				return errors.New("no variable found in the provided text")
			}
			userTypeStr := matchedVariable[2]
			v.AddDependency(
				module.Name,
				userTypeStr,
			)
		}
	}
	return nil
}

func (v *VerilogFile) createDependencyMap() {
	v.DependencyMap = make(map[string]*DependencyNode)
	for _, module := range v.Modules {
		v.DependencyMap[module.Name] = &DependencyNode{
			Name:       module.Name,
			DependsOn:  []string{},
			DependedBy: []string{},
		}
	}
	for _, structName := range v.Structs {
		v.DependencyMap[structName.Name] = &DependencyNode{
			Name:       structName.Name,
			DependsOn:  []string{},
			DependedBy: []string{},
		}
	}
	for _, className := range v.Classes {
		v.DependencyMap[className.Name] = &DependencyNode{
			Name:       className.Name,
			DependsOn:  []string{},
			DependedBy: []string{},
		}
	}
	for _, interfaceName := range v.Interfaces {
		v.DependencyMap[interfaceName.Name] = &DependencyNode{
			Name:       interfaceName.Name,
			DependsOn:  []string{},
			DependedBy: []string{},
		}
	}
	for _, packageName := range v.Packages {
		v.DependencyMap[packageName.Name] = &DependencyNode{
			Name:       packageName.Name,
			DependsOn:  []string{},
			DependedBy: []string{},
		}
	}
	for _, typedef := range v.Typedefs {
		v.DependencyMap[typedef.Name] = &DependencyNode{
			Name:       typedef.Name,
			DependsOn:  []string{},
			DependedBy: []string{},
		}
	}
}

func removeEmptyLines(content string) string {
	lines := strings.Split(content, "\n")
	var nonEmptyLines []string
	for _, line := range lines {
		if strings.TrimSpace(line) != "" {
			nonEmptyLines = append(nonEmptyLines, line)
		}
	}
	return strings.Join(nonEmptyLines, "\n")
}

func removeComments(content string) string {
	// Remove single-line comments
	content = regexp.MustCompile(`(?Um)//\s.*$`).ReplaceAllString(content, "")
	// Remove multi-line comments
	content = regexp.MustCompile(`(?U)/\*[\s\S]*\*/`).ReplaceAllString(content, "")
	return content
}

func cleanText(text string) string {
	text = removeComments(text)
	text = removeEmptyLines(text)
	return text
}

func ParseVerilog(content string, verbose int) (*VerilogFile, error) {
	logger = utils.NewDebugLogger(verbose)
	content = cleanText(content)
	verilogFile := &VerilogFile{}
	err := verilogFile.parseTypedefs(content)
	if err != nil {
		return nil, fmt.Errorf("failed to parse typedefs: %v", err)
	}
	err = verilogFile.parseStructs(content, true)
	if err != nil {
		return nil, fmt.Errorf("failed to parse structs: %v", err)
	}
	err = verilogFile.parseClasses(content)
	if err != nil {
		return nil, fmt.Errorf("failed to parse classes: %v", err)
	}
	err = verilogFile.parseStructs(content, false)
	if err != nil {
		return nil, fmt.Errorf("failed to parse structs: %v", err)
	}
	err = verilogFile.parseModules(content)
	if err != nil {
		return nil, fmt.Errorf("failed to parse modules: %v", err)
	}
	err = verilogFile.parseInterfaces(content)
	if err != nil {
		return nil, fmt.Errorf("failed to parse interfaces: %v", err)
	}
	err = verilogFile.parsePackages(content)
	if err != nil {
		return nil, fmt.Errorf("failed to parse packages: %v", err)
	}
	verilogFile.createDependencyMap()
	err = verilogFile.typeDependenciesParser()
	if err != nil {
		return nil, fmt.Errorf("failed to parse dependencies: %v", err)
	}
	return verilogFile, nil
}

// matchInterfaceInstantiationsFromString finds interface instantiations in the form "interface_name instance_name();" or "interface_name instance_name(params);"
func matchInterfaceInstantiationsFromString(vf *VerilogFile, content string) []string {
	interfaceNames := []string{}
	for _, iface := range vf.Interfaces {
		interfaceNames = append(interfaceNames, iface.Name)
	}

	if len(interfaceNames) == 0 {
		return []string{}
	}

	// Create regex pattern to match interface instantiations like "test_if iface_inst();" or "MyInterface my_if (clk_in);"
	// Also handles parameterized interfaces like "parameterized_if #(.WIDTH(16)) param_if_inst (.clk(clk));"
	// Use (?s) flag to make . match newlines, and don't anchor to line start since instantiations are often indented
	// Use [^;]* instead of [^)]* to handle nested parentheses (e.g., ".clk(clk)" inside the port list)
	// Pattern: interface_name [optional #(params)] instance_name (port_connections);
	// For the parameter section, we use [^#;]* to match everything until we see another # or ;
	interfaceNamesConcat := strings.Join(interfaceNames, "|")
	regexpString := fmt.Sprintf(
		`(?s)(%s)(?:\s*#[^#;]*?)?\s+\w+\s*\([^;]*\)\s*;`,
		interfaceNamesConcat,
	)
	regex := regexp.MustCompile(regexpString)

	matches := regex.FindAllStringSubmatch(content, -1)
	foundInterfaces := []string{}

	for _, match := range matches {
		if len(match) >= 2 {
			interfaceName := match[1]
			foundInterfaces = append(foundInterfaces, interfaceName)
		}
	}

	return foundInterfaces
}

// matchModuleInstantiationsFromString finds module instantiations in the form "module_name instance_name(...);"
func matchModuleInstantiationsFromString(vf *VerilogFile, content string) []string {
	moduleNames := []string{}
	for _, module := range vf.Modules {
		moduleNames = append(moduleNames, module.Name)
	}

	if len(moduleNames) == 0 {
		return []string{}
	}

	// Create regex pattern to match module instantiations like "base_adder inst_name(...)"
	// This pattern matches: module_name instance_name (...);
	// where (...) can contain any parameter/port connections across multiple lines
	moduleNamesConcat := strings.Join(moduleNames, "|")
	// Use (?s) flag to make . match newlines, and don't anchor to line start since instantiations are often indented
	regexpString := fmt.Sprintf(`(?s)(%s)\s+\w+\s*\([^;]*\)\s*;`, moduleNamesConcat)
	regex := regexp.MustCompile(regexpString)

	matches := regex.FindAllStringSubmatch(content, -1)
	foundModules := []string{}

	for _, match := range matches {
		if len(match) >= 2 {
			moduleName := match[1]
			foundModules = append(foundModules, moduleName)
		}
	}

	return foundModules
}

// matchPackageImportsFromString finds package import statements in the form "import package_name::*;" or "import package_name::item;"
func matchPackageImportsFromString(vf *VerilogFile, content string) []string {
	packageNames := []string{}
	for _, pkg := range vf.Packages {
		packageNames = append(packageNames, pkg.Name)
	}

	if len(packageNames) == 0 {
		return []string{}
	}

	// Create regex pattern to match import statements like "import operation_pkg::*;" or "import operation_pkg::item;"
	// Pattern matches: import package_name::
	packageNamesConcat := strings.Join(packageNames, "|")
	regexpString := fmt.Sprintf(`(?m)^\s*import\s+(%s)::\s*(?:\*|[\w]+)\s*;`, packageNamesConcat)
	regex := regexp.MustCompile(regexpString)

	matches := regex.FindAllStringSubmatch(content, -1)
	foundPackages := []string{}

	for _, match := range matches {
		if len(match) >= 2 {
			packageName := match[1]
			foundPackages = append(foundPackages, packageName)
		}
	}

	return foundPackages
}

// matchClassInstantiationsFromString finds class instantiations in the form "ClassName obj = new(...)" or "obj = new(...)" where obj was declared as ClassName
func matchClassInstantiationsFromString(vf *VerilogFile, content string) []string {
	classNames := []string{}
	for _, class := range vf.Classes {
		classNames = append(classNames, class.Name)
	}

	if len(classNames) == 0 {
		return []string{}
	}

	// Pre-process content to remove comments and string literals to avoid false matches
	cleanContent := removeCommentsAndStrings(content)

	foundClasses := []string{}

	// Pattern 1: Direct instantiation with declaration "ClassName obj = new(...)"
	classNamesConcat := strings.Join(classNames, "|")
	// This pattern matches: ClassName [#(...)] variable_name = new(...);
	// Handle nested parentheses in parameter lists using a more flexible approach
	regexpString1 := fmt.Sprintf(
		`(?s)\b(%s)(?:\s*#[^=]*?)?\s+\w+\s*=\s*new\s*\([^;]*\)\s*;`,
		classNamesConcat,
	)
	regex1 := regexp.MustCompile(regexpString1)
	matches1 := regex1.FindAllStringSubmatch(cleanContent, -1)

	for _, match := range matches1 {
		if len(match) >= 2 {
			className := match[1]
			// Avoid duplicates
			found := false
			for _, existing := range foundClasses {
				if existing == className {
					found = true
					break
				}
			}
			if !found {
				foundClasses = append(foundClasses, className)
			}
		}
	}

	// Pattern 2: Look for variable declarations and then find instantiations "obj = new(...)"
	// First, find all class variable declarations with word boundaries
	classVarRegex := fmt.Sprintf(`(?m)^\s*\b(%s)\b\s+(\w+)\s*(?:\[[^\]]*\])?\s*;`, classNamesConcat)
	varRegex := regexp.MustCompile(classVarRegex)
	varMatches := varRegex.FindAllStringSubmatch(cleanContent, -1)

	// Build a map of variable names to their class types
	varToClass := make(map[string]string)
	for _, varMatch := range varMatches {
		if len(varMatch) >= 3 {
			className := varMatch[1]
			varName := varMatch[2]
			varToClass[varName] = className
		}
	}

	// Pattern 3: Look for instantiations of declared class variables "variable_name = new(...)"
	// Handle array access patterns like array_obj[i] = new()
	for varName, className := range varToClass {
		instantiationRegex := fmt.Sprintf(
			`(?s)\b%s(?:\[[^\]]*\])?\s*=\s*new\s*\([^;]*\)\s*;`,
			varName,
		)
		instRegex := regexp.MustCompile(instantiationRegex)
		if instRegex.MatchString(cleanContent) {
			// Avoid duplicates
			found := false
			for _, existing := range foundClasses {
				if existing == className {
					found = true
					break
				}
			}
			if !found {
				foundClasses = append(foundClasses, className)
			}
		}
	}

	return foundClasses
}

// removeCommentsAndStrings removes single-line comments, multi-line comments, and string literals
// to avoid false matches in class instantiation detection
func removeCommentsAndStrings(content string) string {
	content = removeComments(content)
	// Remove string literals (both single and double quoted)
	stringLiteral := regexp.MustCompile(`"[^"\\]*(?:\\.[^"\\]*)*"|'[^'\\]*(?:\\.[^'\\]*)*'`)
	content = stringLiteral.ReplaceAllString(content, `""`)

	return content
}

// removeTaskClassVariablesFromScopes removes variables that are declared in task or class scopes
// from all scope nodes, but keeps them in the main variablesMap
func removeTaskClassVariablesFromScopes(scopeNode *ScopeNode, taskClassVars map[string]bool) {
	if scopeNode == nil {
		return
	}

	// Remove task/class variables from current scope
	for varName := range taskClassVars {
		delete(scopeNode.Variables, varName)
	}

	// Recursively process children
	for _, child := range scopeNode.Children {
		removeTaskClassVariablesFromScopes(child, taskClassVars)
	}
}

// detectTaskClassScopeVariables detects variables that are declared inside task or class scopes
// This is a helper function primarily used for testing
func detectTaskClassScopeVariables(content string) map[string]bool {
	taskClassVars := make(map[string]bool)

	lines := strings.Split(content, "\n")
	insideTaskOrClass := false
	taskClassStartLevel := -1

	for _, line := range lines {
		trimmedLine := strings.TrimSpace(line)
		line = strings.ReplaceAll(line, "\t", "    ")
		indentation := (len(line) - len(strings.TrimLeft(line, " "))) / 4

		// Check if we're entering a task or class scope
		if !insideTaskOrClass && taskClassRegex.MatchString(trimmedLine) {
			insideTaskOrClass = true
			taskClassStartLevel = indentation
			continue
		}

		// Check if we're exiting a task or class scope
		if insideTaskOrClass && indentation <= taskClassStartLevel && trimmedLine != "" {
			if strings.Contains(trimmedLine, "endtask") ||
				strings.Contains(trimmedLine, "endclass") {
				insideTaskOrClass = false
				taskClassStartLevel = -1
				continue
			}
		}

		// If we're inside a task or class, check for variable declarations
		if insideTaskOrClass {
			matchedVariable := generalVariableRegex.FindStringSubmatch(line)
			if len(matchedVariable) >= 6 {
				// Extract variable names from the declaration
				for _, decl := range strings.Split(matchedVariable[5], ",") {
					decl = strings.TrimSpace(decl)
					if decl == "" {
						continue
					}
					arrayMatch := matchArraysFromString(decl)
					if len(arrayMatch) >= 2 {
						varName := strings.TrimSpace(arrayMatch[1])
						if varName != "" {
							taskClassVars[varName] = true
						}
					}
				}
			}
		}
	}

	return taskClassVars
}
