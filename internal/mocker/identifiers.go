package mocker

import (
	"fmt"
	"log"
	"math/rand"
	"regexp"
	"strconv"
	"strings"

	"github.com/toby-bro/pfuzz/pkg/utils"
)

// EnumDefinition represents an extracted enum type
type EnumDefinition struct {
	Name     string
	Package  string
	Values   []string
	FullPath string // Package::EnumName format
}

// DetectEnumCasts identifies all enum casts in the SystemVerilog file
func DetectEnumCasts(filename string) []EnumCast {
	content, err := utils.ReadFileContent(filename)
	if err != nil {
		return nil
	}

	// Updated regex to better capture enum types with namespaces (e.g. ibex_pkg::rv32m_e)
	enumCastRegex := regexp.MustCompile(`(\w+(?:::\w+)?)'?\(([^)]+)\)`)

	var casts []EnumCast
	lines := strings.Split(content, "\n")

	for _, line := range lines {
		matches := enumCastRegex.FindAllStringSubmatch(line, -1)
		for _, match := range matches {
			if len(match) == 3 {
				cast := EnumCast{
					Line:       strings.TrimSpace(line),
					EnumType:   match[1],
					Expression: match[2],
					DefaultVal: GetPlausibleValue(match[1]),
				}
				casts = append(casts, cast)
			}
		}
	}

	return casts
}

// ExtractEnumTypes extracts all enum types from content
func ExtractEnumTypes(content string) []EnumDefinition {
	var enums []EnumDefinition

	// Find already defined enums to avoid redefining them
	definedEnums := extractLocallyDefinedEnums(content)

	// Find all patterns like package::enum_name
	enumRefRegex := regexp.MustCompile(`(\w+)::(\w+_[et])`)

	// Also look for imported packages and used enum types
	importRegex := regexp.MustCompile(`import\s+(\w+)::\*;`)

	// Find references to enum types without package qualifier
	enumTypeRegex := regexp.MustCompile(`\b(operation_t|[\w_]+_[et])\b`)

	// Get unique matches
	enumMap := make(map[string]EnumDefinition)

	// First check for explicit imports
	importMatches := importRegex.FindAllStringSubmatch(content, -1)
	for _, match := range importMatches {
		if len(match) >= 2 {
			pkgName := match[1]
			// Look for uses of enums from this package
			enumRefRegex := regexp.MustCompile(pkgName + "::(\\w+)")
			enumTypeMatches := enumRefRegex.FindAllStringSubmatch(content, -1)

			for _, enumMatch := range enumTypeMatches {
				if len(enumMatch) >= 2 {
					enumName := enumMatch[1]
					fullPath := fmt.Sprintf("%s::%s", pkgName, enumName)

					// Skip if already processed or defined
					if _, exists := enumMap[fullPath]; exists || isEnumDefined(pkgName, enumName, definedEnums) {
						continue
					}

					// Create enum definition with placeholder values
					enum := EnumDefinition{
						Name:     enumName,
						Package:  pkgName,
						FullPath: fullPath,
						Values:   inferEnumValuesFromUsage(content, enumName),
					}

					enumMap[fullPath] = enum
				}
			}
		}
	}

	// Check for explicit enum references with package::enum format
	matches := enumRefRegex.FindAllStringSubmatch(content, -1)
	for _, match := range matches {
		if len(match) >= 3 {
			pkgName := match[1]
			enumName := match[2]
			fullPath := fmt.Sprintf("%s::%s", pkgName, enumName)

			// Skip if already processed
			if _, exists := enumMap[fullPath]; exists {
				continue
			}

			// Skip if it's already defined in the module
			if isEnumDefined(pkgName, enumName, definedEnums) {
				log.Printf("Skipping already defined enum: %s::%s", pkgName, enumName)
				continue
			}

			// Create enum definition with values inferred from usage
			enum := EnumDefinition{
				Name:     enumName,
				Package:  pkgName,
				FullPath: fullPath,
				Values:   inferEnumValuesFromUsage(content, enumName),
			}

			enumMap[fullPath] = enum
		}
	}

	// Handle standalone enum types that might be used without package qualifier
	typeMatches := enumTypeRegex.FindAllStringSubmatch(content, -1)
	for _, match := range typeMatches {
		if len(match) >= 2 {
			enumName := match[1]

			// Skip if already handled by package::enum format
			alreadyHandled := false
			for path := range enumMap {
				if strings.HasSuffix(path, "::"+enumName) {
					alreadyHandled = true
					break
				}
			}

			if alreadyHandled {
				continue
			}

			// For standalone enums, try to infer package from context
			pkgName := inferPackageNameFromContext(content, enumName)
			fullPath := fmt.Sprintf("%s::%s", pkgName, enumName)

			// Skip if already processed or defined
			if _, exists := enumMap[fullPath]; exists {
				continue
			}

			// Create enum definition with values inferred from usage
			enum := EnumDefinition{
				Name:     enumName,
				Package:  pkgName,
				FullPath: fullPath,
				Values:   inferEnumValuesFromUsage(content, enumName),
			}

			enumMap[fullPath] = enum
		}
	}

	// Convert map to slice
	for _, enum := range enumMap {
		enums = append(enums, enum)
	}

	return enums
}

// inferPackageNameFromContext tries to determine the package name for an enum type
func inferPackageNameFromContext(content, enumName string) string {
	// Look for import statements
	importRegex := regexp.MustCompile(`import\s+(\w+)::\*;`)
	matches := importRegex.FindAllStringSubmatch(content, -1)

	if len(matches) > 0 {
		// If we have imports, use the first one as a guess
		return matches[0][1]
	}

	// For operation_t specifically, use operation_pkg
	if enumName == "operation_t" {
		return "operation_pkg"
	}

	// Create a package name based on the enum name
	if strings.HasSuffix(enumName, "_t") {
		return strings.TrimSuffix(enumName, "_t") + "_pkg"
	}
	if strings.HasSuffix(enumName, "_e") {
		return strings.TrimSuffix(enumName, "_e") + "_pkg"
	}

	// Default package name
	return "enum_pkg"
}

// inferEnumValuesFromUsage analyzes code to infer enum values based on usage
func inferEnumValuesFromUsage(content, enumName string) []string {
	var values []string

	// Track already added values to avoid duplicates
	addedValues := make(map[string]bool)

	// Look for direct assignments using this enum (e.g., val1 = VAL_A;)
	assignmentRegex := regexp.MustCompile(`\w+\s*=\s*(\w+)\s*;`)
	assignMatches := assignmentRegex.FindAllStringSubmatch(content, -1)

	for _, match := range assignMatches {
		if len(match) >= 2 {
			value := strings.TrimSpace(match[1])
			if !addedValues[value] && isLikelyEnumValue(value) {
				addedValues[value] = true
				values = append(values, value)
			}
		}
	}

	// Look for case statements using this enum
	caseRegex := regexp.MustCompile(`case\s*\([^)]*\)\s*([^:]+):`)
	caseMatches := caseRegex.FindAllStringSubmatch(content, -1)

	for _, match := range caseMatches {
		if len(match) >= 2 {
			value := strings.TrimSpace(match[1])
			if !addedValues[value] && isLikelyEnumValue(value) {
				addedValues[value] = true
				values = append(values, value)
			}
		}
	}

	// Look for comparisons with enum constants like "== OPCODE_BRANCH"
	comparisonRegex := regexp.MustCompile(`==\s*(\w+)`)
	compMatches := comparisonRegex.FindAllStringSubmatch(content, -1)

	for _, match := range compMatches {
		if len(match) >= 2 {
			value := strings.TrimSpace(match[1])
			if !addedValues[value] && isLikelyEnumValue(value) {
				addedValues[value] = true
				values = append(values, value)
			}
		}
	}

	// Find enum constants used on the right side of comparisons like "OPCODE_BRANCH =="
	rightCompRegex := regexp.MustCompile(`(\w+)\s*==`)
	rightMatches := rightCompRegex.FindAllStringSubmatch(content, -1)

	for _, match := range rightMatches {
		if len(match) >= 2 {
			value := strings.TrimSpace(match[1])
			if !addedValues[value] && isLikelyEnumValue(value) {
				addedValues[value] = true
				values = append(values, value)
			}
		}
	}

	// If we didn't find any values, add common VAL_X patterns often used in tests
	if len(values) == 0 {
		// Add common enum value patterns
		commonValues := []string{"VAL_A", "VAL_B", "VAL_C", "VAL_D"}
		for _, val := range commonValues {
			if strings.Contains(content, val) {
				addedValues[val] = true
				values = append(values, val)
			}
		}
	}

	// Always add a default/invalid value if it doesn't already exist
	if !addedValues["INVALID"] {
		values = append(values, "INVALID")
	}

	// Ensure we have at least some default values
	if len(values) == 0 {
		values = generatePlausibleEnumValues(enumName)
	}

	return values
}

// extractEnumPrefix gets a reasonable prefix for enum values based on the enum name
func extractEnumPrefix(enumName string) string {
	// Strip common suffixes
	name := enumName
	if strings.HasSuffix(name, "_t") {
		name = strings.TrimSuffix(name, "_t")
	} else if strings.HasSuffix(name, "_e") {
		name = strings.TrimSuffix(name, "_e")
	}

	return strings.ToUpper(name)
}

// isLikelyEnumValue checks if a string looks like an enum value (all caps, no special chars)
func isLikelyEnumValue(value string) bool {
	if value == "" {
		return false
	}

	// Consider uppercase identifiers as likely enum values
	upperRegex := regexp.MustCompile(`^[A-Z][A-Z0-9_]*$`)
	if upperRegex.MatchString(value) {
		return true
	}

	// Consider VAL_X patterns as enum values
	valPattern := regexp.MustCompile(`^VAL_[A-Z0-9]$`)
	return valPattern.MatchString(value)
}

// Helper function to check if an enum is already defined
func isEnumDefined(pkgName, enumName string, definedEnums map[string]bool) bool {
	key := fmt.Sprintf("%s::%s", pkgName, enumName)
	return definedEnums[key]
}

// extractLocallyDefinedEnums finds all enums already defined in the file
func extractLocallyDefinedEnums(content string) map[string]bool {
	definedEnums := make(map[string]bool)

	// Look for package definitions
	packageRegex := regexp.MustCompile(`package\s+(\w+)\s*;([\s\S]*?)endpackage`)
	pkgMatches := packageRegex.FindAllStringSubmatch(content, -1)

	for _, pkgMatch := range pkgMatches {
		if len(pkgMatch) >= 3 {
			pkgName := pkgMatch[1]
			pkgContent := pkgMatch[2]

			// Mark the package itself as defined
			definedEnums[pkgName+"::"] = true

			// Find typedefs within this package
			typedefRegex := regexp.MustCompile(`typedef\s+enum\s+[\s\S]*?}\s*(\w+_[et])\s*;`)
			typeMatches := typedefRegex.FindAllStringSubmatch(pkgContent, -1)

			for _, typeMatch := range typeMatches {
				if len(typeMatch) >= 2 {
					enumName := typeMatch[1]
					key := fmt.Sprintf("%s::%s", pkgName, enumName)
					definedEnums[key] = true
					log.Printf("Found already defined enum: %s", key)
				}
			}
		}
	}

	return definedEnums
}

// generatePlausibleEnumValues creates reasonable values for an enum based on its name
func generatePlausibleEnumValues(enumName string) []string {
	// Different enum types get different plausible values
	enumNameLower := strings.ToLower(enumName)

	if strings.Contains(enumNameLower, "opcode") {
		return []string{"OPCODE_LOAD", "OPCODE_STORE", "OPCODE_BRANCH", "OPCODE_JALR",
			"OPCODE_JAL", "OPCODE_OP_IMM", "OPCODE_OP", "OPCODE_SYSTEM"}
	}

	if strings.Contains(enumNameLower, "imm") && strings.Contains(enumNameLower, "sel") {
		return []string{"IMM_A_ZERO", "IMM_A_CURR", "IMM_B_I", "IMM_B_S", "IMM_B_B",
			"IMM_B_U", "IMM_B_J", "IMM_B_INCR_PC", "IMM_B_INCR_ADDR"}
	}

	if strings.Contains(enumNameLower, "op_a_sel") {
		return []string{"OP_A_REG_A", "OP_A_FWD", "OP_A_CURRPC", "OP_A_IMM"}
	}

	if strings.Contains(enumNameLower, "op_b_sel") {
		return []string{"OP_B_REG_B", "OP_B_FWD", "OP_B_IMM", "OP_B_NONE"}
	}

	if strings.Contains(enumNameLower, "md_op") {
		return []string{"MD_OP_MULL", "MD_OP_MULH", "MD_OP_DIV", "MD_OP_REM"}
	}

	if strings.Contains(enumNameLower, "csr") && strings.Contains(enumNameLower, "op") {
		return []string{"CSR_OP_READ", "CSR_OP_WRITE", "CSR_OP_SET", "CSR_OP_CLEAR"}
	}

	if strings.Contains(enumNameLower, "rv32") {
		if strings.Contains(enumNameLower, "m") {
			return []string{"RV32MNone", "RV32MSlow", "RV32MFast", "RV32MEmbedded"}
		}
		if strings.Contains(enumNameLower, "b") {
			return []string{"RV32BNone", "RV32BBalanced", "RV32BOTEarlGrey", "RV32BFull"}
		}
	}

	if strings.Contains(enumNameLower, "alu_op") {
		return []string{"ALU_ADD", "ALU_SUB", "ALU_XOR", "ALU_OR", "ALU_AND",
			"ALU_SRA", "ALU_SRL", "ALU_SLL", "ALU_LT", "ALU_LTU", "ALU_GE",
			"ALU_GEU", "ALU_EQ", "ALU_NE"}
	}

	// Default: generate generic values
	values := []string{
		strings.ToUpper(enumName) + "_VAL0",
		strings.ToUpper(enumName) + "_VAL1",
		strings.ToUpper(enumName) + "_VAL2",
		strings.ToUpper(enumName) + "_VAL3",
	}

	return values
}

// DetectUndefinedIdentifiers identifies undefined identifiers in the SystemVerilog file
func DetectUndefinedIdentifiers(filename string) []UndefinedIdentifier {
	content, err := utils.ReadFileContent(filename)
	if err != nil {
		return nil
	}

	knownKeywords := map[string]bool{
		"module": true, "input": true, "output": true, "logic": true,
		"always_comb": true, "assign": true, "begin": true, "end": true,
		"if": true, "else": true, "case": true, "endcase": true,
		"unique": true, "default": true, "parameter": true,
		"enum": true, "typedef": true, "struct": true, "union": true,
		"localparam": true, "always_ff": true, "posedge": true,
		"negedge": true, "initial": true, "for": true, "while": true,
		"repeat": true, "forever": true, "break": true, "continue": true,
		"return": true, "assert": true, "assume": true, "cover": true,
		"sequence": true, "property": true, "disable": true,
		"assert_property": true, "task": true, "endtask": true, "inout": true,
		"reg": true, "wire": true, "bit": true, "byte": true, "int": true,
	}

	// Extract locally defined types from typedefs
	locallyDefinedTypes := extractLocallyDefinedTypes(content)
	for t := range locallyDefinedTypes {
		knownKeywords[t] = true
	}

	// Also extract module names and parameters as they're effectively defined
	extractModuleDeclarations(content, knownKeywords)

	var undefinedVars []UndefinedIdentifier
	lines := strings.Split(content, "\n")

	identifierRegex := regexp.MustCompile(`\b([A-Za-z_][A-Za-z0-9_]*)\b`)

	for _, line := range lines {
		if strings.Contains(line, "//") || strings.Contains(line, "/*") {
			continue
		}

		matches := identifierRegex.FindAllStringSubmatch(line, -1)
		for _, match := range matches {
			identifier := match[1]
			if !knownKeywords[identifier] && strings.Contains(line, identifier) {
				if strings.HasSuffix(identifier, "_e") || strings.HasSuffix(identifier, "_t") ||
					strings.HasPrefix(identifier, "OPCODE_") {
					undefinedVars = append(undefinedVars, UndefinedIdentifier{
						Line:    strings.TrimSpace(line),
						Name:    identifier,
						Context: InferContext(line),
					})
				}
			}
		}
	}

	return undefinedVars
}

// extractLocallyDefinedTypes extracts locally defined types from typedefs
func extractLocallyDefinedTypes(content string) map[string]bool {
	definedTypes := make(map[string]bool)

	// First, strip comments to avoid confusion
	content = regexp.MustCompile(`//.*$|/\*[\s\S]*?\*/`).ReplaceAllString(content, "")

	// Handle simple typedef cases first (non-enum)
	simpleTypedefRegex := regexp.MustCompile(`typedef\s+[a-zA-Z0-9_\[\]:]+\s+([a-zA-Z0-9_]+)\s*;`)
	matches := simpleTypedefRegex.FindAllStringSubmatch(content, -1)
	for _, match := range matches {
		if len(match) >= 2 {
			definedTypes[match[1]] = true
		}
	}

	// Handle enum typedefs with better multi-line processing
	lines := strings.Split(content, "\n")
	inEnum := false
	enumBuffer := ""

	for _, line := range lines {
		trimmedLine := strings.TrimSpace(line)

		// Skip empty lines
		if trimmedLine == "" {
			continue
		}

		// Check if we're starting a new enum declaration
		if strings.Contains(trimmedLine, "typedef enum") {
			inEnum = true
			enumBuffer = trimmedLine

			// If the enum declaration is on a single line, process it immediately
			if strings.Contains(trimmedLine, "}") && strings.Contains(trimmedLine, ";") {
				enumNameMatch := regexp.MustCompile(`}\s*([a-zA-Z0-9_]+)\s*;`).FindStringSubmatch(trimmedLine)
				if len(enumNameMatch) >= 2 {
					definedTypes[enumNameMatch[1]] = true
				}
				inEnum = false
				enumBuffer = ""
			}
		} else if inEnum {
			// Append current line to enum buffer
			enumBuffer += " " + trimmedLine

			// Check if this line contains the end of the enum declaration
			if strings.Contains(trimmedLine, "}") {
				// Find the type name after the closing brace
				enumNameMatch := regexp.MustCompile(`}\s*([a-zA-Z0-9_]+)\s*;`).FindStringSubmatch(enumBuffer)
				if len(enumNameMatch) >= 2 {
					definedTypes[enumNameMatch[1]] = true
				} else {
					// Try with just the current line if the combined buffer doesn't match
					enumNameMatch = regexp.MustCompile(`}\s*([a-zA-Z0-9_]+)\s*;`).FindStringSubmatch(trimmedLine)
					if len(enumNameMatch) >= 2 {
						definedTypes[enumNameMatch[1]] = true
					}
				}
				inEnum = false
				enumBuffer = ""
			}
		}
	}

	// Add support for detecting imported enums like ibex_pkg::*
	importedEnumRegex := regexp.MustCompile(`(\w+)::(\w+_[et])`)
	importedMatches := importedEnumRegex.FindAllStringSubmatch(content, -1)
	for _, match := range importedMatches {
		if len(match) >= 3 {
			pkgName := match[1]
			enumName := match[2]
			definedTypes[pkgName+"::"+enumName] = true
			// Also add just the enum name as it might be imported
			definedTypes[enumName] = true
		}
	}

	// Add more robust detection for struct typedefs
	structRegex := regexp.MustCompile(`typedef\s+struct\s+\{[^}]*\}\s*([a-zA-Z0-9_]+)\s*;`)
	structMatches := structRegex.FindAllStringSubmatch(content, -1)
	for _, match := range structMatches {
		if len(match) >= 2 {
			definedTypes[match[1]] = true
		}
	}

	if len(definedTypes) > 0 {
		log.Println("Defined types found:")
		for t := range definedTypes {
			log.Printf("  %s\n", t)
		}
	}

	return definedTypes
}

// Helper function to extract module declarations and parameters
func extractModuleDeclarations(content string, knownKeywords map[string]bool) {
	// Get module names
	moduleRegex := regexp.MustCompile(`\bmodule\s+([a-zA-Z0-9_]+)`)
	matches := moduleRegex.FindAllStringSubmatch(content, -1)
	for _, match := range matches {
		if len(match) >= 2 {
			knownKeywords[match[1]] = true
		}
	}

	// Get parameter names
	paramRegex := regexp.MustCompile(`\bparameter\s+([a-zA-Z0-9_]+)`)
	matches = paramRegex.FindAllStringSubmatch(content, -1)
	for _, match := range matches {
		if len(match) >= 2 {
			knownKeywords[match[1]] = true
		}
	}

	// Get signal names from port list and declarations
	signalRegex := regexp.MustCompile(`\b(?:input|output|inout)\s+(?:logic|wire|reg)?\s*(?:\[[^\]]+\])?\s*([a-zA-Z0-9_]+)`)
	matches = signalRegex.FindAllStringSubmatch(content, -1)
	for _, match := range matches {
		if len(match) >= 2 {
			knownKeywords[match[1]] = true
		}
	}
}

// InferContext attempts to determine the context of an identifier
func InferContext(line string) string {
	if strings.Contains(line, "opcode_e") {
		return "opcode"
	} else if strings.Contains(line, "assign") {
		return "signal"
	} else if strings.Contains(line, "parameter") {
		return "parameter"
	}
	return "unknown"
}

// GetPlausibleValue returns a plausible value for an enum type
func GetPlausibleValue(enumType string) string {
	// Enhanced to handle package::enum format
	if strings.Contains(enumType, "::") {
		parts := strings.Split(enumType, "::")
		pkgName := parts[0]
		enumName := parts[1]

		// Generate a generic enum value with package namespace
		return fmt.Sprintf("%s::%s_VALUE0", pkgName, extractEnumPrefix(enumName))
	}

	// For non-package enums, fall back to existing logic
	width := utils.InferBitWidth("")
	switch {
	case strings.HasSuffix(enumType, "_e"):
		return strconv.Itoa(rand.Intn(8))
	case strings.HasSuffix(enumType, "_t"):
		return utils.GenerateRandomBitString(width)
	default:
		if rand.Float32() < 0.5 {
			return utils.GenerateRandomBitString(width)
		}
		return utils.GenerateRandomHexString(width)
	}
}

// MockIdentifier provides a mock value for an undefined identifier
func MockIdentifier(id UndefinedIdentifier) string {
	width := utils.InferBitWidth(id.Context)

	switch {
	case strings.HasPrefix(id.Name, "OPCODE_"):
		return utils.GenerateRandomBitString(7)
	case strings.Contains(id.Context, "enum"):
		return strconv.Itoa(rand.Intn(8))
	case strings.Contains(id.Context, "logic"):
		return utils.GenerateRandomBitString(width)
	default:
		if rand.Float32() < 0.5 {
			return utils.GenerateRandomBitString(width)
		}
		return utils.GenerateRandomHexString(width)
	}
}

// MockEnumCast provides a mock value for an enum cast while preserving type information
func MockEnumCast(cast EnumCast) string {
	// If the expression is already a literal, just return it
	if regexp.MustCompile(`^[0-9]+('?[bdh][0-9a-fA-F_]+)?$`).MatchString(cast.Expression) {
		return cast.Expression
	}

	// For any enum types (identified by suffix _t or _e), use a default bit width
	if strings.HasSuffix(cast.EnumType, "_t") || strings.HasSuffix(cast.EnumType, "_e") {
		// Infer reasonable bit width based on enum name or context
		width := inferEnumBitWidth(cast.EnumType, cast.Line)

		// Generate a value with the right width
		return fmt.Sprintf("%d'b%s", width, strings.Repeat("0", width))
	}

	// Default behavior for unknown types
	return GetPlausibleValue(cast.EnumType)
}

// inferEnumBitWidth determines a reasonable bit width for an enum type
func inferEnumBitWidth(enumType, context string) int {
	// Check if we can determine width from context
	widthRegex := regexp.MustCompile(`\[(\d+):0\]`)
	if matches := widthRegex.FindStringSubmatch(context); matches != nil {
		if width, err := strconv.Atoi(matches[1]); err == nil {
			return width + 1
		}
	}

	// Check if enum name contains hints about its width
	lowerType := strings.ToLower(enumType)

	// Common widths for different types of enums
	if strings.Contains(lowerType, "op") && strings.Contains(lowerType, "code") {
		return 7 // Typical opcode width
	} else if strings.Contains(lowerType, "oper") {
		return 3 // Typical operation enum width
	} else if strings.Contains(lowerType, "mode") || strings.Contains(lowerType, "state") {
		return 2 // Typical mode/state enum width
	}

	// Default to 3 bits which is common for small enums
	return 3
}

// ReplaceMockedEnumCasts replaces all enum casts in the content with mocked values
func ReplaceMockedEnumCasts(content string, enumCasts []EnumCast) string {
	// First, extract and protect parameter declarations from modification
	paramDecls := make(map[string]string)
	paramRegex := regexp.MustCompile(`(parameter\s+)([^=;]+)(=\s*[^;]+;)`)

	// Find and store parameter declarations
	matches := paramRegex.FindAllStringSubmatch(content, -1)
	for i, match := range matches {
		if len(match) >= 4 {
			key := fmt.Sprintf("__PARAM_%d__", i)
			paramDecls[key] = match[0]
			content = strings.Replace(content, match[0], key, 1)
		}
	}

	// Never replace enum casts - we want to preserve the SystemVerilog type casting
	// The import statements will ensure these types are available

	// Restore parameter declarations
	for key, value := range paramDecls {
		content = strings.Replace(content, key, value, 1)
	}

	return content
}

// GenerateEnumDefinitions creates enum definition code for all detected enums
func GenerateEnumDefinitions(enums []EnumDefinition) string {
	if len(enums) == 0 {
		return ""
	}

	var result strings.Builder
	result.WriteString("\n// Mock enum definitions for imported types\n")

	// First, detect if we have duplicate package names to handle them specially
	pkgCount := make(map[string]int)
	for _, enum := range enums {
		pkgCount[enum.Package]++
	}

	// Group enums by package
	packageEnums := make(map[string][]EnumDefinition)
	for _, enum := range enums {
		packageEnums[enum.Package] = append(packageEnums[enum.Package], enum)
	}

	// Generate each package with its enums
	for pkgName, pkgEnums := range packageEnums {
		// Create package
		result.WriteString(fmt.Sprintf("package %s;\n", pkgName))

		// Define all enums in this package
		for _, enum := range pkgEnums {
			// Determine appropriate bit width for the enum
			bitWidth := inferEnumBitWidth(enum.Name, "")

			// RISC-V opcode enums need 7 bits
			if strings.Contains(strings.ToLower(enum.Name), "opcode") {
				bitWidth = 7
			}

			result.WriteString(fmt.Sprintf("    // Mock definition for %s::%s\n", enum.Package, enum.Name))
			result.WriteString(fmt.Sprintf("    typedef enum logic [%d:0] {\n", bitWidth-1))

			// Add enum values with appropriate encoding
			for i, val := range enum.Values {
				comma := ","
				if i == len(enum.Values)-1 {
					comma = ""
				}

				// Handle special enum value types
				if strings.Contains(strings.ToLower(enum.Name), "opcode") && strings.HasPrefix(val, "OPCODE_") {
					var opcodeValue string
					// Use standard RISC-V opcodes
					switch val {
					case "OPCODE_LOAD":
						opcodeValue = "7'b0000011" // 0x03
					case "OPCODE_STORE":
						opcodeValue = "7'b0100011" // 0x23
					// ...existing code for opcodes...
					default:
						opcodeValue = fmt.Sprintf("%d'd%d", bitWidth, i)
					}
					result.WriteString(fmt.Sprintf("        %s = %s%s\n", val, opcodeValue, comma))
				} else {
					result.WriteString(fmt.Sprintf("        %s = %d'd%d%s\n", val, bitWidth, i, comma))
				}
			}

			result.WriteString(fmt.Sprintf("    } %s;\n\n", enum.Name))
		}

		result.WriteString(fmt.Sprintf("endpackage : %s\n\n", pkgName))
	}

	return result.String()
}
