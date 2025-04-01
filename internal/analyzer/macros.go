package analyzer

import (
	"regexp"
	"strings"
)

// DetectMacros identifies all macros in the SystemVerilog content
func DetectMacros(content string) []string {
	var macros []string
	// Match macro invocations starting with ` or $ and include statements
	macroRegex := regexp.MustCompile("(`|\\$)\\w+|`include\\s+\"[^\"]+\"")

	matches := macroRegex.FindAllString(content, -1)
	for _, match := range matches {
		macros = append(macros, match)
	}

	return macros
}

// RemoveMacros removes all occurrences of the specified macros from the content
func RemoveMacros(content string, macros []string) string {
	lines := strings.Split(content, "\n")
	var result []string

	for _, line := range lines {
		shouldKeep := true
		for _, macro := range macros {
			if strings.Contains(line, macro) {
				shouldKeep = false
				break
			}
		}
		if shouldKeep {
			result = append(result, line)
		}
	}

	return strings.Join(result, "\n")
}
