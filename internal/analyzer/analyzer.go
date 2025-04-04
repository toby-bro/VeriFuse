package analyzer

import (
	"fmt"
	"log"
	"regexp"
	"strings"

	"github.com/jns/pfuzz/pkg/utils"
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

	// Detect undefined identifiers
	undefinedVars := DetectUndefinedIdentifiers(filepath)
	if len(undefinedVars) > 0 {
		log.Println("Detected undefined identifiers and their mocked values:")
		for _, undef := range undefinedVars {
			mockedValue := MockIdentifier(undef)
			log.Printf("  Name: %s, Context: %s -> Mocked: %s\n",
				undef.Name, undef.Context, mockedValue)
		}

		for _, undef := range undefinedVars {
			content = strings.Replace(content, undef.Name,
				MockIdentifier(undef), -1)
		}
	}

	// Rename the module
	moduleRegex := regexp.MustCompile(`module\s+(\w+)\s*\(`)
	content = moduleRegex.ReplaceAllString(content, "module ${1}_mocked (")

	return content, nil
}
