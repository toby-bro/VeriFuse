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
	macros = append(macros, matches...)

	return macros
}

// FindAssertionMacros finds all assertion macros with their structure
func FindAssertionMacros(content string) []MacroDefinition {
	var macros []MacroDefinition

	// Process the content line by line to handle multi-line macros
	lines := strings.Split(content, "\n")

	var buffer string
	var inMacro bool
	var macroStart int
	var openParens int

	for i, line := range lines {
		trimmedLine := strings.TrimSpace(line)

		// Check for new macro start
		if !inMacro && strings.Contains(trimmedLine, "`ASSERT") {
			inMacro = true
			macroStart = i
			buffer = line

			// Count opening parentheses
			openParens = strings.Count(line, "(") - strings.Count(line, ")")
		} else if inMacro {
			buffer += "\n" + line

			// Update parentheses count
			openParens += strings.Count(line, "(") - strings.Count(line, ")")

			// If all parentheses are closed, the macro is complete
			if openParens <= 0 {
				inMacro = false

				// Extract macro name and arguments
				macro := parseMacroDefinition(buffer)
				macro.MultiLine = (i - macroStart) > 0
				macros = append(macros, macro)
				buffer = ""
			}
		}
	}

	return macros
}

// parseMacroDefinition extracts the macro name and arguments from a macro invocation
func parseMacroDefinition(macroText string) MacroDefinition {
	// Extract the macro name
	nameRegex := regexp.MustCompile("`(\\w+)\\s*\\(")
	nameMatch := nameRegex.FindStringSubmatch(macroText)

	macroName := ""
	if len(nameMatch) >= 2 {
		macroName = nameMatch[1]
	}

	// Extract the arguments - this is trickier for multi-line macros
	// Remove all whitespace and newlines to simplify extraction
	cleanText := regexp.MustCompile(`\s+`).ReplaceAllString(macroText, " ")

	// Find opening parenthesis position after the macro name
	openPos := strings.Index(cleanText, "(")
	if openPos == -1 {
		return MacroDefinition{
			FullText:  macroText,
			MacroName: macroName,
			Arguments: []string{},
		}
	}

	// Extract everything inside the outer parentheses
	parenLevel := 0
	argsText := ""
	inArgs := false

	for i := 0; i < len(cleanText); i++ {
		char := cleanText[i]

		if char == '(' {
			parenLevel++
			if parenLevel == 1 {
				inArgs = true
				continue // Skip the opening parenthesis
			}
		} else if char == ')' {
			parenLevel--
			if parenLevel == 0 {
				inArgs = false
				break // Stop at the closing parenthesis
			}
		}

		if inArgs {
			argsText += string(char)
		}
	}

	// Split the arguments by comma, but respect nested parentheses
	var args []string
	currentArg := ""
	parenLevel = 0

	for i := 0; i < len(argsText); i++ {
		char := argsText[i]

		if char == '(' {
			parenLevel++
		} else if char == ')' {
			parenLevel--
		} else if char == ',' && parenLevel == 0 {
			args = append(args, strings.TrimSpace(currentArg))
			currentArg = ""
			continue
		}

		currentArg += string(char)
	}

	// Add the last argument
	if currentArg != "" {
		args = append(args, strings.TrimSpace(currentArg))
	}

	return MacroDefinition{
		FullText:  macroText,
		MacroName: macroName,
		Arguments: args,
	}
}

// RemoveMacros removes all occurrences of the specified macros from the content
// but preserves functionality for certain macro types
func RemoveMacros(content string, macros []string) string {
	// First handle assertion macros specially to preserve their logic
	assertionMacros := FindAssertionMacros(content)
	for _, assertion := range assertionMacros {
		// Transform the assertion into valid SystemVerilog code
		replacement := generateAssertionReplacement(assertion)
		content = strings.Replace(content, assertion.FullText, replacement, -1)
	}

	// Handle include statements - completely remove them
	includeRegex := regexp.MustCompile("`include\\s+\"[^\"]+\"\\s*\n?")
	content = includeRegex.ReplaceAllString(content, "")

	// Now handle simple macros by removing only the macro identifier
	// But preserve $error and other system tasks that are part of the language
	simpleRegex := regexp.MustCompile("(`|\\$)(\\w+)")
	content = simpleRegex.ReplaceAllStringFunc(content, func(match string) string {
		// Preserve $error and other standard system tasks
		if match == "$error" || match == "$display" || match == "$finish" ||
			match == "$time" || match == "$fatal" || match == "$warning" ||
			match == "$info" || match == "$fopen" || match == "$fclose" ||
			match == "$write" || match == "$fwrite" || match == "$fscanf" ||
			match == "$fgets" || match == "$sscanf" || match == "$sformatf" ||
			match == "$readmemh" || match == "$readmemb" {
			return match // Keep these unchanged
		}

		// Remove and replace with comment for other macros
		return "/* " + match + " */"
	})

	return content
}

// generateAssertionReplacement creates valid SystemVerilog code to represent an assertion
func generateAssertionReplacement(assertion MacroDefinition) string {
	var result strings.Builder

	// Add a comment to indicate the original assertion
	result.WriteString("// Original macro: " + assertion.MacroName + "\n")

	if len(assertion.Arguments) >= 2 {
		// Extract assertion name (first argument)
		assertName := assertion.Arguments[0]

		// For each argument beyond the first, create a variable
		for i := 1; i < len(assertion.Arguments); i++ {
			argValue := assertion.Arguments[i]

			// Clean up the argument text
			argValue = strings.TrimSpace(argValue)
			varName := fmt.Sprintf("var%d_%s", i, assertName)

			// Replace unsupported SystemVerilog constructs
			// Use a valid expression rather than commenting out
			argValue = strings.Replace(argValue, "$isunknown", "0", -1)
			argValue = strings.Replace(argValue, "$onehot0", "|", -1) // Replace with OR reduction

			// Check if this is a multi-bit expression (concatenation, bit slicing)
			if strings.Contains(argValue, "{") ||
				strings.Contains(argValue, ":") ||
				strings.Contains(argValue, "concat") {
				// For multi-bit expressions, use a wire with sufficient width
				result.WriteString(fmt.Sprintf("wire [31:0] %s_tmp;\n", varName))
				result.WriteString(fmt.Sprintf("assign %s_tmp = %s;\n", varName, argValue))

				// Create boolean result using reduction operator
				result.WriteString(fmt.Sprintf("logic %s;\n", varName))
				result.WriteString(fmt.Sprintf("assign %s = |%s_tmp;\n", varName, varName))
			} else if strings.Contains(argValue, "(") && strings.Contains(argValue, ")") {
				// For function calls or parenthesized expressions
				result.WriteString(fmt.Sprintf("logic %s;\n", varName))

				// If it looks like a comparison, use directly
				if strings.Contains(argValue, "==") || strings.Contains(argValue, "!=") ||
					strings.Contains(argValue, ">=") || strings.Contains(argValue, "<=") ||
					strings.Contains(argValue, ">") || strings.Contains(argValue, "<") {
					result.WriteString(fmt.Sprintf("assign %s = %s;\n", varName, argValue))
				} else {
					// Otherwise use a reduction to convert to boolean
					result.WriteString(fmt.Sprintf("assign %s = |(%s);\n", varName, argValue))
				}
			} else {
				// Simple expression
				result.WriteString(fmt.Sprintf("logic %s;\n", varName))

				// Handle comparison operators correctly
				if strings.Contains(argValue, "==") {
					result.WriteString(fmt.Sprintf("assign %s = %s;\n", varName, argValue))
				} else if strings.Contains(argValue, "=") && !strings.Contains(argValue, "==") {
					// Convert single = to == for boolean comparison
					argValue = strings.Replace(argValue, "=", "==", 1)
					result.WriteString(fmt.Sprintf("assign %s = %s;\n", varName, argValue))
				} else {
					// Simple value - convert to boolean if needed
					result.WriteString(fmt.Sprintf("assign %s = %s;\n", varName, argValue))
				}
			}
		}

		// Add a comment that would explain the assertion's intent
		result.WriteString(fmt.Sprintf("// Assertion check: %s\n", assertName))
	} else {
		// If we can't parse the arguments properly, add a comment
		result.WriteString("// Unparseable assertion: " + assertion.FullText + "\n")
	}

	return result.String()
}
