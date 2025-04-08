package analyzer

import (
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
// by simply commenting them out
func RemoveMacros(content string, macros []string) string {
	// First handle assertion macros specially - comment them out with their context
	assertionMacros := FindAssertionMacros(content)
	for _, assertion := range assertionMacros {
		// Simply comment out the entire assertion
		replacement := generateAssertionReplacement(assertion)
		content = strings.Replace(content, assertion.FullText, replacement, -1)
	}

	// Handle include statements - completely remove them
	includeRegex := regexp.MustCompile("`include\\s+\"[^\"]+\"\\s*\n?")
	content = includeRegex.ReplaceAllString(content, "")

	// Now handle simple macros by commenting them out
	simpleRegex := regexp.MustCompile("(`|\\$)(\\w+)")
	content = simpleRegex.ReplaceAllStringFunc(content, func(match string) string {
		// Preserve standard system tasks
		if match == "$error" || match == "$display" || match == "$finish" ||
			match == "$time" || match == "$fatal" || match == "$warning" ||
			match == "$info" || match == "$fopen" || match == "$fclose" ||
			match == "$write" || match == "$fwrite" || match == "$fscanf" ||
			match == "$fgets" || match == "$sscanf" || match == "$sformatf" ||
			match == "$readmemh" || match == "$readmemb" {
			return match // Keep these unchanged
		}

		// Comment out the macro
		return "/* " + match + " */"
	})

	return content
}

// generateAssertionReplacement creates a simple comment for an assertion macro
func generateAssertionReplacement(assertion MacroDefinition) string {
	// Just convert the assertion to a comment
	// Use //-- instead of // to make the comment more visible and avoid nested comment issues
	var result strings.Builder

	result.WriteString("//-- Commented assertion macro: " + assertion.MacroName + "\n")
	result.WriteString("//-- Original code: \n")

	// Split the original text into lines and comment each line
	lines := strings.Split(assertion.FullText, "\n")
	for _, line := range lines {
		result.WriteString("//-- " + line + "\n")
	}

	return result.String()
}
