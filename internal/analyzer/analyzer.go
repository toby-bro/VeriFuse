package analyzer

import (
	"fmt"
	"log"
	"regexp"
	"strings"

	"github.com/toby-bro/pfuzz/pkg/utils"
)

// EnumCast represents a detected enum cast in SystemVerilog
type EnumCast struct {
	Line       string
	EnumType   string
	Expression string
	DefaultVal string
}

// UndefinedIdentifier represents a detected undefined identifier
type UndefinedIdentifier struct {
	Line    string
	Name    string
	Context string
}

// AnalyzeVerilogFile analyzes a SystemVerilog file and returns processed content
func AnalyzeVerilogFile(filepath string) (string, error) {
	content, err := utils.ReadFileContent(filepath)
	if err != nil {
		return "", fmt.Errorf("failed to read verilog file: %v", err)
	}
	// Remove comments from the content
	content = utils.RemoveComments(content)

	// Remove unique from case statements
	content = utils.RemoveUniqueCases(content)

	// Extract enum types for later processing
	enums := ExtractEnumTypes(content)
	if len(enums) > 0 {
		log.Println("Detected enum types that will be mocked:")
		for _, enum := range enums {
			log.Printf("  %s::%s with %d values\n", enum.Package, enum.Name, len(enum.Values))
		}

		// Generate enum definitions
		enumDefs := GenerateEnumDefinitions(enums)

		// Add Verilator lint pragma to disable width warnings at the top of the file
		if !strings.Contains(content, "verilator lint_off WIDTHEXPAND") {
			content = "/* verilator lint_off WIDTHEXPAND */\n" + content
		}

		// Insert the enum definitions before the module declaration
		modulePos := strings.Index(content, "module ")
		if modulePos > 0 {
			content = content[:modulePos] + enumDefs + content[modulePos:]
		}
	}

	// Detect and remove macros
	macros := DetectMacros(content)
	if len(macros) > 0 {
		log.Println("Detected macros that will be removed:")
		for _, macro := range macros {
			log.Printf("  %s\n", macro)
		}
		content = RemoveMacros(content, macros)
	}

	// Detect enum casts
	enumCasts := DetectEnumCasts(filepath)
	if len(enumCasts) > 0 {
		log.Println("Detected enum casts and their mocked values:")
		for _, cast := range enumCasts {
			mockedValue := MockEnumCast(cast)
			log.Printf("  Type: %s, Expression: %s -> Mocked: %s\n",
				cast.EnumType, cast.Expression, mockedValue)
		}
		content = ReplaceMockedEnumCasts(content, enumCasts)
	}

	// Detect undefined identifiers (handle these after enum processing)
	undefinedVars := DetectUndefinedIdentifiers(filepath)
	if len(undefinedVars) > 0 {
		log.Println("Detected undefined identifiers and their mocked values:")
		for _, undef := range undefinedVars {
			mockedValue := MockIdentifier(undef)
			log.Printf("  Name: %s, Context: %s -> Mocked: %s\n",
				undef.Name, undef.Context, mockedValue)
		}

		for _, undef := range undefinedVars {
			// Only mock certain types of identifiers, and avoid ones that will be handled by our enum system
			if !strings.Contains(undef.Name, "::") &&
				!isEnumIdentifier(undef.Name, enums) &&
				(strings.HasSuffix(undef.Name, "_e") ||
					strings.HasSuffix(undef.Name, "_t") ||
					strings.Contains(undef.Context, "parameter")) {
				content = strings.Replace(content, undef.Name,
					MockIdentifier(undef), -1)
			}
		}
	}

	// Rename the module
	moduleRegex := regexp.MustCompile(`module\s+(\w+)\s*(\#\s*\([^)]*\))?\s*\(`)
	content = moduleRegex.ReplaceAllString(content, "module ${1}_mocked${2} (")

	return content, nil
}

// isEnumIdentifier checks if a name is already defined in our enum definitions
func isEnumIdentifier(name string, enums []EnumDefinition) bool {
	for _, enum := range enums {
		if enum.Name == name {
			return true
		}

		// Also check enum values
		for _, val := range enum.Values {
			if val == name {
				return true
			}
		}
	}
	return false
}

// Helper function to check if content already has package definitions for our enums
func containsDuplicatePackages(content string, enums []EnumDefinition) bool {
	for _, enum := range enums {
		// Look for package definitions like "package ibex_pkg;"
		packagePattern := fmt.Sprintf("package\\s+%s\\s*;", enum.Package)
		packageRegex := regexp.MustCompile(packagePattern)
		if packageRegex.MatchString(content) {
			return true
		}
	}
	return false
}
