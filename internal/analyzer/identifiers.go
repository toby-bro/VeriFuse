package analyzer

import (
	"fmt"
	"math/rand"
	"regexp"
	"strconv"
	"strings"

	"github.com/toby-bro/pfuzz/pkg/utils"
)

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
	}

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
	if strings.Contains(enumType, "opcode_e") {
		return "instr[6:0]"
	}

	width := utils.InferBitWidth("")
	switch {
	case strings.HasSuffix(enumType, "_e"):
		return fmt.Sprintf("%d", rand.Intn(8))
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
		return fmt.Sprintf("%d", rand.Intn(8))
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

	// Determine if we need to preserve a specific bit width
	widthMatch := regexp.MustCompile(`(\d+)'([bdh])([0-9a-fA-F_]+)`).FindStringSubmatch(cast.DefaultVal)

	// If we have a specific width in the default value, preserve it
	if len(widthMatch) > 3 {
		width, _ := strconv.Atoi(widthMatch[1])
		base := widthMatch[2]
		// Generate a value with the same width and format
		switch base {
		case "b":
			return fmt.Sprintf("%d'b%s", width, utils.GenerateRandomBitsOfWidth(width))
		case "h":
			return fmt.Sprintf("%d'h%s", width, utils.GenerateRandomHexOfWidth(width))
		case "d":
			return fmt.Sprintf("%d'd%d", width, rand.Intn(1<<width))
		}
	}

	// Default behavior
	return GetPlausibleValue(cast.EnumType)
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

	// Add Verilator lint pragma to disable width warnings at the top of the file
	if !strings.Contains(content, "verilator lint_off WIDTHEXPAND") {
		pragmaPos := strings.Index(content, "module ")
		if pragmaPos > 0 {
			content = content[:pragmaPos] +
				"/* verilator lint_off WIDTHEXPAND */\n" +
				content[pragmaPos:]
		}
	}

	// Process enum casts - now they won't affect parameter declarations
	for _, cast := range enumCasts {
		// Skip parameter declarations - they're already protected
		if strings.Contains(cast.Line, "parameter") {
			continue
		}

		// For non-parameter casting expressions, handle enum casts specially
		// Replace the entire casting expression with just the inner expression for opcode enums
		if strings.Contains(cast.EnumType, "opcode_e") && strings.Contains(cast.Expression, "instr") {
			// For opcode-related enums, just use the inner expression without the cast
			pattern := fmt.Sprintf(`%s'\\(%s\\)`, regexp.QuoteMeta(cast.EnumType), regexp.QuoteMeta(cast.Expression))
			r := regexp.MustCompile(pattern)
			content = r.ReplaceAllString(content, cast.Expression)
		} else {
			// For other casts, completely replace the cast with a simple value of correct width
			pattern := fmt.Sprintf(`%s'\\(%s\\)`, regexp.QuoteMeta(cast.EnumType), regexp.QuoteMeta(cast.Expression))
			r := regexp.MustCompile(pattern)

			// Try to extract width from the enum type if it's a literal like '7'h78'
			width := 7 // Default width for enums
			if match := regexp.MustCompile(`^(\d+)'[hbd]`).FindStringSubmatch(cast.EnumType); len(match) > 1 {
				if w, err := strconv.Atoi(match[1]); err == nil {
					width = w
				}
			}

			// Generate a simple value of the right width
			replacementValue := fmt.Sprintf("%d'h%s", width, utils.GenerateRandomHexOfWidth(width))
			content = r.ReplaceAllString(content, replacementValue)
		}
	}

	// Restore parameter declarations
	for key, value := range paramDecls {
		content = strings.Replace(content, key, value, 1)
	}

	return content
}
