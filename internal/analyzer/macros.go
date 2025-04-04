package analyzer

import (
	"fmt"
	"regexp"
	"strings"
)

// MacroDefinition represents a detected macro and its components
type MacroDefinition struct {
	FullText  string
	MacroName string
	Arguments []string
	MultiLine bool
}

// DetectMacros identifies all macros in the SystemVerilog content
func DetectMacros(content string) []string {
	var macros []string
	// Match simple macros invocations starting with ` or $
	macroRegex := regexp.MustCompile("(`|\\$)\\w+|`include\\s+\"[^\"]+\"")

	matches := macroRegex.FindAllString(content, -1)
	for _, match := range matches {
		macros = append(macros, match)
	}

	return macros
}

// FindAssertionMacros finds all assertion macros with their structure
func FindAssertionMacros(content string) []MacroDefinition {
	var macros []MacroDefinition

	// Pattern to match assertion macros and capture their arguments
	assertPattern := regexp.MustCompile("(?s)(`ASSERT\\w*)\\s*\\((\\w+)\\s*,([^\\)]+)\\)")

	matches := assertPattern.FindAllStringSubmatch(content, -1)
	for _, match := range matches {
		if len(match) >= 4 {
			macro := MacroDefinition{
				FullText:  match[0],
				MacroName: match[1],
				Arguments: []string{match[2], strings.TrimSpace(match[3])},
				MultiLine: strings.Contains(match[0], "\n"),
			}
			macros = append(macros, macro)
		}
	}

	return macros
}

// RemoveMacros removes all occurrences of the specified macros from the content
// but preserves functionality for certain macro types
func RemoveMacros(content string, macros []string) string {
	// First handle assertion macros specially to preserve their logic
	assertionMacros := FindAssertionMacros(content)
	for _, assertion := range assertionMacros {
		// Transform the assertion into a Verilog comment that preserves the assertion logic
		replacement := fmt.Sprintf("// Assertion: %s - %s\n// %s",
			assertion.Arguments[0], assertion.MacroName, assertion.Arguments[1])
		content = strings.Replace(content, assertion.FullText, replacement, -1)
	}
	// Handle include statements - completely remove them
	includeRegex := regexp.MustCompile("`include\\s+\"[^\"]+\"\\s*\n?")
	content = includeRegex.ReplaceAllString(content, "")

	// Now handle simple macros by removing only the macro identifier
	simpleRegex := regexp.MustCompile("(`|\\$)(\\w+)")
	content = simpleRegex.ReplaceAllString(content, "/* $1$2 */")

	return content
}
