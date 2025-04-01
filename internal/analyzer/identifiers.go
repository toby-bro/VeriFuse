package analyzer

import (
	"fmt"
	"math/rand"
	"regexp"
	"strings"

	"github.com/jns/pfuzz/pkg/utils"
)

// DetectEnumCasts identifies all enum casts in the SystemVerilog file
func DetectEnumCasts(filename string) []EnumCast {
	content, err := utils.ReadFileContent(filename)
	if err != nil {
		return nil
	}

	enumCastRegex := regexp.MustCompile(`(\w+)'?\(([^)]+)\)`)

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

// MockEnumCast provides a mock value for an enum cast
func MockEnumCast(cast EnumCast) string {
	if regexp.MustCompile(`^[0-9]+('?[bdh][0-9a-fA-F_]+)?$`).MatchString(cast.Expression) {
		return cast.Expression
	}

	return GetPlausibleValue(cast.EnumType)
}

// ReplaceMockedEnumCasts replaces enum casts with mocked values
func ReplaceMockedEnumCasts(content string, casts []EnumCast) string {
	lines := strings.Split(content, "\n")
	for i, line := range lines {
		for _, cast := range casts {
			if strings.Contains(line, cast.Line) {
				originalCast := fmt.Sprintf("%s'(%s)", cast.EnumType, cast.Expression)
				mockedValue := MockEnumCast(cast)
				lines[i] = strings.Replace(line, originalCast, mockedValue, 1)
			}
		}
	}
	return strings.Join(lines, "\n")
}
