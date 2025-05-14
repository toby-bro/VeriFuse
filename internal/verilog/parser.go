package verilog

import (
	"bufio"
	"errors"
	"fmt"
	"regexp"
	"strconv"
	"strings"

	"github.com/toby-bro/pfuzz/pkg/utils"
)

var logger *utils.DebugLogger

// TODO: #5 Improve the type for structs, enums, userdefined types...
func GetType(portTypeString string) PortType {
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
	`(?m)module\s+(\w+)\s*(?:#\s*\(([\s\S]*?)\))?\s*\(([^\)]*?)\);(?:\s((?:(?:\s\s|\t\s*)+.*)+))?\sendmodule`,
)

var generalClassRegex = regexp.MustCompile(
	`(?m)(?:(virtual)\s+)?class\s+(\w+)\s*(?:extends\s+(\w+))?(?:\s+#\s*\(([\s\S]*?)\))?;\s((?:(?:\t\s*|\s\s+).*)+)\sendclass`,
)

var generalStructRegex = regexp.MustCompile(
	`(?m)typedef\s+struct\s+(?:packed\s+)\{((?:\s+.*)+)\}\s+(\w+);`,
)

var baseTypes = `reg|wire|integer|real|time|realtime|logic|bit|byte|shortint|int|longint|shortreal|string|struct|enum`

var baseTypesRegex = regexp.MustCompile(fmt.Sprintf(`(?m)^\s*(%s)\s*$`, baseTypes))

var variableRegexTemplate = `(?m)^(\s*)(?:\w+\s+)?(%s)\s+(?:(?:(\[[\w\-]+:[\w\-]+\])+|(unsigned))\s+)?(?:#\(\w+\)\s+)?((?:(?:(?:\w+(?:\s+\[[^\]]+\])?\s*,\s*)+)\s*)*(?:\w+(?:\s+\[[^\]]+\])?))(?:\s+=\s+new\(.*\))?\s*;`

var generalPortRegex = regexp.MustCompile(fmt.Sprintf(
	`^\s*(input|output|inout)\s+(?:(%s)\s+)?(?:(signed|unsigned)\s+)?(\[\s*[\w\-\+\:\s]+\s*\])?\s*(\w+)\s*(?:,|;)`,
	baseTypes,
))

var generalParameterRegex = regexp.MustCompile(fmt.Sprintf(
	`(?m)^\s*(?:(localparam|parameter)\s+)?(?:(%s)\s+)?(?:(?:unsigned|signed)\s+)?(\w+)(?:\s*(=)\s*(.+))?\s*(?:,|;)?$`,
	baseTypes,
))

var arrayRegex = regexp.MustCompile(`(?m)(\w+)(?:\s+(\[[^\]]+\]))?`)

var ansiPortRegex = regexp.MustCompile(
	`^\s*(?:(input|output|inout)\s+)?(?:(` +
		baseTypes +
		`)\s+)?(?:(signed|unsigned)\s+)?` +
		`(?:(\[\s*[\w\-\+\:\s]+\s*\])\s+)?` +
		`(\w+)\s*$`,
)

var simplePortRegex = regexp.MustCompile(
	`^\s*(?:\.\s*(\w+)\s*\()?\s*(\w+)\s*\)?\s*$`,
)

// TODO: #15 improve to replace the initial \w with rand local const ... and I don't know what not Also add the support for declarations with , for many decls
var generalVariableRegex = regexp.MustCompile(
	fmt.Sprintf(
		variableRegexTemplate,
		baseTypes,
	),
)

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

func MatchArraysFromString(content string) []string {
	return arrayRegex.FindStringSubmatch(content)
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

func MatchAllParametersFromString(param string) []string {
	return generalParameterRegex.FindStringSubmatch(param)
}

// Utility functions for bit width parsing
func ParseRange(rangeStr string, parameters map[string]Parameter) (int, error) {
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
func parsePortDeclaration(line string, parameters map[string]Parameter) (*Port, bool) {
	var matches []string
	var direction PortDirection

	line = strings.TrimSpace(line) // Ensure leading/trailing whitespace is removed

	matches = generalPortRegex.FindStringSubmatch(line)
	if len(matches) != 6 {
		return nil, false // Not a matching port declaration line
	}
	direction = GetPortDirection(strings.TrimSpace(matches[1]))
	portType := GetType(strings.TrimSpace(matches[2]))
	signedStr := strings.TrimSpace(matches[3])
	rangeStr := strings.TrimSpace(matches[4])
	portName := strings.TrimSpace(matches[5])

	if portType == UNKNOWN {
		portType = LOGIC // Default type if not specified (SystemVerilog) or wire (Verilog)
	}
	isSigned := (signedStr == "signed")
	width, err := ParseRange(rangeStr, parameters)
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
	headerPorts := make(map[string]Port)
	headerPortOrder := []string{}

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
			portStr := strings.TrimSpace(matches[2])
			portType := GetType(portStr)
			signedStr := strings.TrimSpace(matches[3])
			rangeStr := strings.TrimSpace(matches[4])
			portName = strings.TrimSpace(matches[5])

			if directionStr == "" && portStr == "" && signedStr == "" && rangeStr == "" {
				if len(headerPortOrder) == 0 {
					logger.Warn("Header port declaration '%s' is empty.", portDecl)
					continue
				}
				// Port is the same as the last port
				precedingPort := headerPorts[headerPortOrder[len(headerPortOrder)-1]]
				port = Port{
					Name:      portName,
					Direction: precedingPort.Direction,
					Type:      precedingPort.Type,
					Width:     precedingPort.Width,
					IsSigned:  precedingPort.IsSigned,
				}
			} else {
				isSigned := (signedStr == "signed")
				width, err := ParseRange(rangeStr, parameters)
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
				direction := GetPortDirection(directionStr)

				// Handle default widths for types if no range specified AND parseRange didn't error
				if false && width == 1 && rangeStr == "" && err == nil {
					width = GetWidthForType(portType)
				}

				port = Port{
					Name:      portName,
					Direction: direction,
					Type:      portType,
					Width:     width,
					IsSigned:  isSigned,
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
			port = Port{Name: portName, Width: 0, Type: UNKNOWN, Direction: INTERNAL, IsSigned: false} // Sensible defaults
		} else {
			logger.Warn("Could not parse port declaration fragment in header: '%s'\n", portDecl)
			continue // Skip if we can't extract a name
		}

		if portName != "" {
			if _, exists := headerPorts[portName]; exists {
				logger.Warn(
					"Duplicate port name '%s' detected in module header.\n",
					portName,
				)
			}
			headerPorts[portName] = port // Store parsed/placeholder port
			headerPortOrder = append(headerPortOrder, portName)
		}
	}

	return headerPorts, headerPortOrder
}

// extractNonANSIPortDeclarations scans the provided content for non-ANSI port declarations in the module content
func extractNonANSIPortDeclarations(
	content string,
	parameters map[string]Parameter,
) (map[string]Port, error) {
	scanner := bufio.NewScanner(strings.NewReader(content))
	parsedPortsMap := make(map[string]Port)

	for scanner.Scan() {
		trimmedLine := strings.TrimSpace(scanner.Text())

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
			logger.Warn("Port '%s' in order but not found in header map.", nameInHeader)
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

		finalPorts = append(finalPorts, finalPort)
		processedPorts[nameInHeader] = true
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
			logger.Warn("Skipping %s as failed to parse ports: %v", moduleName, err)
			continue // Skip this module if port parsing fails
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

func parseParameters(parameterListString string) ([]Parameter, error) {
	params := strings.Split(parameterListString, ",")
	parametersList := []Parameter{}

	for _, paramStr := range params {
		trimmedParamStr := strings.TrimSpace(paramStr)
		if trimmedParamStr == "" {
			continue
		}

		matches := MatchAllParametersFromString(trimmedParamStr)

		if len(matches) == 6 {
			paramLocalityStr := strings.TrimSpace(matches[1])
			paramTypeStr := strings.TrimSpace(matches[2])
			paramName := strings.TrimSpace(matches[3])
			paramValue := ""
			if matches[4] == "=" {
				paramValue = strings.TrimSpace(matches[5])
			}

			if paramName == "" {
				logger.Warn(
					"could not parse parameter fragment, missing parameter name in: '%s'",
					trimmedParamStr,
				)
				continue
			}
			paramType := GetType(paramTypeStr)
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

			parametersList = append(parametersList, Parameter{
				Name:         paramName,
				Type:         paramType,
				DefaultValue: paramValue,
				Localparam:   paramLocality,
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

	headerPorts, headerPortOrder := extractANSIPortDeclarations(portList, paramMap)
	parsedPortsMap, scanErr := extractNonANSIPortDeclarations(
		module.Body,
		paramMap,
	)
	if scanErr != nil {
		logger.Warn("Error during scan for non-ANSI ports: %v", scanErr)
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
		logger.Warn("No ports found or parsed for module %s. Module might have no ports.", module.Name)
	}
	return nil
}

// Be carefull must be parsed third after ParseClass and ParseStruct as the types of the variables might not be defined yet
// TODO: #16 support arrays which will break the current width checking
func ParseVariables(v *VerilogFile,
	content string,
) ([]*Variable, *ScopeNode, error) {
	allMatchedVariables := MatchAllVariablesFromString(content)
	variables := make([]*Variable, 0, len(allMatchedVariables))
	scopeTree := &ScopeNode{
		Level:     0,
		Variables: []*Variable{},
		Children:  []*ScopeNode{},
		Parent:    nil,
	}
	scopeNode := scopeTree
	for _, matchedVariable := range allMatchedVariables {
		if len(matchedVariable) < 4 {
			return nil, nil, errors.New("no variable found in the provided text")
		}
		indent := len(strings.ReplaceAll(matchedVariable[1], "\t", "    ")) / 4
		varType := GetType(matchedVariable[2])
		widthStr := matchedVariable[3]
		width, err := ParseRange(widthStr, nil)
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
		if varType == UNKNOWN {
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
			arrayMatch := MatchArraysFromString(decl)
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
			variables = append(variables, variable)
			if indent == scopeNode.Level {
				scopeNode.Variables = append(scopeNode.Variables, variable)
			} else {
				for scopeNode.Level > indent {
					scopeNode = scopeNode.Parent
				}
				newScopeNode := &ScopeNode{
					Level:     indent,
					Variables: []*Variable{variable},
					Children:  []*ScopeNode{},
					Parent:    scopeNode,
				}
				scopeNode.Children = append(scopeNode.Children, newScopeNode)
				scopeNode = newScopeNode
			}
		}
	}
	return variables, scopeTree, nil
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
			variables, _, err := ParseVariables(v, varList)
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
			userTypeStr := matchedVariable[2]
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
			userTypeStr := matchedVariable[2]
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
	// replace all the // INJECT by  //INJECT
	content = regexp.MustCompile(`//\s*INJECT`).ReplaceAllString(content, "//INJECT")
	// Remove single-line comments
	content = regexp.MustCompile(`(?m)//\s.*$`).ReplaceAllString(content, "")
	// Remove multi-line comments
	content = regexp.MustCompile(`/\*[\s\S]*\*/`).ReplaceAllString(content, "")
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
