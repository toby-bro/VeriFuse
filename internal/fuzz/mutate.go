package fuzz

import (
	"errors"
	"fmt"
	"math/rand"
	"path/filepath"
	"regexp"
	"strings"
	"time"

	"github.com/toby-bro/pfuzz/internal/verilog"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

var (
	snippets   = []string{}
	seededRand = rand.New(rand.NewSource(time.Now().UnixNano()))
)

func ExtractModules(filePath string) (map[string]string, error) {
	fileContent, err := utils.ReadFileContent(filePath)
	if err != nil {
		return nil, fmt.Errorf("failed to read file %s: %v", filePath, err)
	}
	moduleName := ""

	lines := strings.Split(fileContent, "\n")
	allModules := make(map[string]string)
	moduleContent := []string{}

	for _, line := range lines {
		trimmedLine := strings.TrimSpace(line)
		switch {
		case strings.HasPrefix(trimmedLine, "module"):
			// Extract module name, handle potential parameters/ports in declaration
			parts := strings.Fields(trimmedLine)
			if len(parts) >= 2 {
				namePart := parts[1]
				// Remove parameter list #(...) and port list (...) if present
				if idx := strings.IndexAny(namePart, "(#"); idx != -1 {
					namePart = namePart[:idx]
				}
				// Use base filename and extracted name for a unique key
				moduleName = filepath.Base(filePath) + "_" + namePart
				moduleContent = []string{line} // Start collecting with the module line itself
			} else {
				// Malformed module line, reset state just in case
				moduleName = ""
				moduleContent = []string{}
			}
		case strings.HasPrefix(trimmedLine, "endmodule"):
			if moduleName != "" { // Only process if we were inside a module
				moduleContent = append(moduleContent, line) // Add the endmodule line
				allModules[moduleName] = strings.Join(moduleContent, "\n")
				// Reset for the next potential module
				moduleName = ""
				moduleContent = []string{}
			}
			// If moduleName was already "", this endmodule is ignored (e.g., nested or mismatched)
		default:
			if moduleName != "" { // Only append lines if we are inside a module definition
				moduleContent = append(moduleContent, line)
			}
			// Otherwise, ignore lines outside module definitions
		}
	}

	if len(allModules) == 0 {
		return nil, fmt.Errorf("no modules found in file %s", filePath)
	}

	return allModules, nil
}

func LoadSnippets() ([]string, error) {
	snippetsDir := filepath.Join("..", "..", "snippets")
	sourceFiles, err := filepath.Glob(filepath.Join(snippetsDir, "*.sv"))
	if err != nil {
		return nil, err
	}

	allModules := make(map[string]string)
	for _, snippetFile := range sourceFiles {
		modules, err := ExtractModules(snippetFile)
		if err != nil {
			return nil, err
		}
		for name, content := range modules {
			allModules[name] = content
		}
	}
	// Convert map to slice
	snippetList := make([]string, 0, len(allModules))
	for _, content := range allModules {
		snippetList = append(snippetList, content)
	}
	return snippetList, nil
}

func GetSnippets() ([]string, error) {
	if len(snippets) == 0 {
		var err error
		snippets, err = LoadSnippets()
		if err != nil {
			return nil, fmt.Errorf("failed to load snippets: %v", err)
		}
	}
	return snippets, nil
}

func GetRandomSnippet() (string, error) {
	snippets, err := GetSnippets()
	if err != nil {
		return "", fmt.Errorf("failed to get snippets: %v", err)
	}
	if len(snippets) == 0 {
		return "", errors.New("no snippets available")
	}
	randomIndex := utils.RandomInt(0, len(snippets)-1)
	return snippets[randomIndex], nil
}

// InjectSnippet attempts to inject a snippet module instantiation into the original content.
// Uses the verilog parser to understand both original and snippet structures and attempts
// to connect snippet inputs to compatible signals in the original module.
func InjectSnippet(originalContent string, snippet string) (string, error) {
	// 1. Parse Original Content
	originalModule, err := verilog.ParseVerilogContent(
		[]byte(originalContent),
		"",
	)
	if err != nil {
		// If parsing original fails, we cannot reliably inject.
		return originalContent, fmt.Errorf("failed to parse original content: %v", err)
	}
	if originalModule == nil || originalModule.Name == "" {
		return originalContent, errors.New("could not identify module in original content")
	}

	// 2. Parse Snippet Content
	snippetModule, err := verilog.ParseVerilogContent([]byte(snippet), "")
	if err != nil {
		// Attempt fallback like before if full parse fails
		generalModuleRegex := regexp.MustCompile(`module\s+(\w+)`)
		matches := generalModuleRegex.FindStringSubmatch(snippet)
		fallbackName := "unknown_snippet"
		if len(matches) > 1 {
			fallbackName = matches[1]
		}
		fmt.Printf(
			"Warning: Failed to fully parse snippet: %v. Proceeding with fallback name '%s' and no port info.\n",
			err,
			fallbackName,
		)
		snippetModule = &verilog.Module{
			Name:    fallbackName,
			Ports:   []verilog.Port{},
			Content: snippet,
		}
		// Fallback might lead to empty instantiation if no ports are found
	}
	if snippetModule == nil || snippetModule.Name == "" {
		return originalContent, errors.New("failed to identify module name in snippet")
	}

	// 4. Iterate Snippet Ports and Determine Connections/Declarations
	instanceName := fmt.Sprintf("%s_inst_%d", snippetModule.Name, seededRand.Intn(10000))
	instantiation := fmt.Sprintf("%s %s (", snippetModule.Name, instanceName)
	connections := []string{}
	newDeclarations := []string{} // Wires/logic needed for snippet outputs/inouts

	for _, snipPort := range snippetModule.Ports {
		signalName := ""
		foundMatch := false

		// 5. Match Inputs
		if snipPort.Direction == verilog.INPUT {
			// Search original module ports for a compatible match
			for _, origPort := range originalModule.Ports {
				// Check for compatibility (Type, Width, Signedness)
				// Allow connecting snippet input to any original port type for now
				if origPort.Type == snipPort.Type &&
					origPort.Width == snipPort.Width &&
					origPort.IsSigned == snipPort.IsSigned {
					signalName = origPort.Name
					fmt.Printf(
						"    Matching snippet input '%s' to original port '%s'\n",
						snipPort.Name,
						signalName,
					)
					foundMatch = true
					// break // Use the first compatible match found
				}
			}
			// If no compatible port found, generate placeholder
			if !foundMatch {
				signalName = fmt.Sprintf(
					"inj_unconnected_%s_%d",
					strings.ToLower(snipPort.Name),
					seededRand.Intn(100),
				)
				fmt.Printf(
					"    No compatible port found for snippet input '%s'. Using placeholder '%s'.\n",
					snipPort.Name,
					signalName,
				)
				// Optionally, declare this unconnected input? For now, leave it.
			}
		} else { // 6. Handle Outputs/Inouts
			// Generate unique internal signal name
			directionPrefix := "output"
			if snipPort.Direction == verilog.INOUT {
				directionPrefix = "inout"
			}
			signalName = fmt.Sprintf("inj_%s_%s_%d", directionPrefix, strings.ToLower(snipPort.Name), seededRand.Intn(1000))

			// Generate declaration for this internal signal
			widthStr := ""
			if snipPort.Width > 1 {
				widthStr = fmt.Sprintf("[%d:0] ", snipPort.Width-1)
			}
			portType := snipPort.Type
			if portType == "" {
				portType = "logic"
			} // Default
			signedStr := ""
			if snipPort.IsSigned {
				signedStr = "signed "
			}
			newDeclarations = append(newDeclarations, fmt.Sprintf("%s %s%s%s;", portType, signedStr, widthStr, signalName))
			fmt.Printf("    Declaring internal signal '%s' for snippet %s '%s'\n", signalName, directionPrefix, snipPort.Name)
		}

		connections = append(connections, fmt.Sprintf(".%s(%s)", snipPort.Name, signalName))
	}
	instantiation += strings.Join(connections, ", ") + ");"

	// 7. Find Insertion Point in originalContent string
	// Find the start of the original module definition to ensure we insert inside it.
	// Use the parsed actualTargetModule name.
	moduleStartRegexStr := "(?m)^\\s*module\\s+" + regexp.QuoteMeta(originalModule.Name)
	moduleStartRegex := regexp.MustCompile(moduleStartRegexStr)
	moduleStartMatch := moduleStartRegex.FindStringIndex(originalContent)
	if moduleStartMatch == nil {
		return originalContent, fmt.Errorf(
			"could not find start of module '%s' in original content",
			originalModule.Name,
		)
	}

	// Find the endmodule relative to the start of the module
	endModuleRegex := regexp.MustCompile(`(?m)^\s*endmodule`)
	endModuleMatch := endModuleRegex.FindStringIndex(
		originalContent[moduleStartMatch[1]:],
	) // Search after module header

	var insertionPointIndex int
	if endModuleMatch != nil {
		insertionPointIndex = moduleStartMatch[1] + endModuleMatch[0] // Index in originalContent
	} else {
		// Fallback: Insert at the end of the string if endmodule not found (less ideal)
		insertionPointIndex = len(originalContent)
		fmt.Printf("Warning: Could not find 'endmodule' for '%s'. Inserting near end of content.\n", originalModule.Name)
	}

	// Determine indentation for insertion (find indent of the line before endmodule)
	indent := "    " // Default indent
	if insertionPointIndex > 0 {
		prevNewline := strings.LastIndex(originalContent[:insertionPointIndex], "\n")
		if prevNewline != -1 {
			lineBeforeEndmodule := originalContent[prevNewline+1 : insertionPointIndex]
			indentRegex := regexp.MustCompile(`^(\s*)`)
			if matches := indentRegex.FindStringSubmatch(lineBeforeEndmodule); len(matches) > 1 {
				// Use indent of the line itself if endmodule was on its own line,
				// or just grab whitespace if endmodule shared a line (less likely)
				if strings.TrimSpace(lineBeforeEndmodule) == "" ||
					strings.HasPrefix(strings.TrimSpace(lineBeforeEndmodule), "endmodule") {
					indent = matches[1] + "    " // Add typical indent level
				} else {
					indent = matches[1] // Use existing line's indent
				}
			}
		}
	}

	// 8. Construct Result
	var result strings.Builder
	// Add snippet definition *before* the original module
	result.WriteString(snippet)
	result.WriteString("\n\n")

	// Add original content up to insertion point
	result.WriteString(originalContent[:insertionPointIndex])

	// Add new declarations
	if len(newDeclarations) > 0 {
		result.WriteString("\n" + indent + "// Declarations for injected module instance\n")
		for _, decl := range newDeclarations {
			result.WriteString(indent + decl + "\n")
		}
	}

	// Add the instantiation
	result.WriteString(indent + "// Instantiation of injected module\n")
	result.WriteString(indent + instantiation + "\n\n")

	// Add rest of original content
	result.WriteString(originalContent[insertionPointIndex:])

	return result.String(), nil
}

// AddCodeToSnippet attempts to replace the //INJECT marker in a snippet
// with random lines from the original content. Basic draft implementation.
// Returns the modified snippet string.
func AddCodeToSnippet(originalContent, snippet string) (string, error) {
	originalLines := strings.Split(originalContent, "\n")
	snippetLines := strings.Split(snippet, "\n")

	if len(originalLines) < 3 {
		return snippet, errors.New(
			"original content too short to extract code from",
		) // Return original snippet on error
	}

	// Find the //INJECT marker
	injectIndex := -1
	markerIndent := "" // Indent of the marker line itself
	indentRegex := regexp.MustCompile(`^(\s*)`)
	for i, line := range snippetLines {
		if strings.Contains(line, "//INJECT") {
			injectIndex = i
			if matches := indentRegex.FindStringSubmatch(line); len(matches) > 1 {
				markerIndent = matches[1]
			}
			break
		}
	}

	if injectIndex == -1 {
		return snippet, errors.New(
			"snippet does not contain //INJECT marker",
		) // Return original snippet
	}

	// Select 1 to 3 random lines from the original content (excluding module/endmodule/comments/declarations)
	numLinesToInject := utils.RandomInt(1, 3)
	injectedLines := []string{}
	maxAttempts := 30 // Increased attempts
	attempts := 0
	// Lines to skip: comments, module defs, declarations (input, output, wire, reg, logic, parameter, localparam)
	skipLineRegex := regexp.MustCompile(
		`^\s*(?:\/\/|\/\*|\*\/|module|endmodule|input|output|inout|wire|reg|logic|parameter|localparam)\b`,
	)

	// Try to find lines within the main module body if possible
	originalModule, origErr := verilog.ParseVerilogContent(
		[]byte(originalContent),
		"",
	)
	startLine, endLine := 0, len(originalLines)-1
	if origErr == nil && originalModule != nil {
		// Very rough estimate of body lines (after header, before endmodule)
		// This needs better line number info from parser ideally
		moduleHeaderEndApprox := strings.Index(originalContent, ");")
		moduleEndApprox := strings.LastIndex(originalContent, "endmodule")
		if moduleHeaderEndApprox != -1 {
			startLine = strings.Count(originalContent[:moduleHeaderEndApprox], "\n") + 1
		}
		if moduleEndApprox != -1 {
			endLine = strings.Count(originalContent[:moduleEndApprox], "\n")
		}
	}

	for len(injectedLines) < numLinesToInject && attempts < maxAttempts {
		attempts++
		// Try to pick lines from the estimated body
		idx := utils.RandomInt(startLine, endLine)
		if idx >= len(originalLines) {
			continue // Bounds check
		}

		line := originalLines[idx]
		trimmedLine := strings.TrimSpace(line)

		// Check if line is non-empty and not a comment/declaration/module boundary
		if trimmedLine != "" && !skipLineRegex.MatchString(line) {
			// Basic check to avoid injecting simple end/begin keywords alone
			if trimmedLine != "end" && trimmedLine != "begin" &&
				!strings.HasPrefix(trimmedLine, "end ") {
				injectedLines = append(injectedLines, line)
			}
		}
	}

	if len(injectedLines) == 0 {
		// If no lines selected, just remove the marker
		fmt.Println("    No suitable lines found to inject. Removing //INJECT marker.")
		return strings.Join(
			append(snippetLines[:injectIndex], snippetLines[injectIndex+1:]...),
			"\n",
		), nil
	}

	// Replace the //INJECT line with the selected lines
	var result strings.Builder
	result.WriteString(strings.Join(snippetLines[:injectIndex], "\n"))
	// Keep newline before injected code only if injectIndex > 0
	if injectIndex > 0 {
		result.WriteString("\n")
	}

	fmt.Printf("    Injecting %d lines into snippet...\n", len(injectedLines))
	for _, line := range injectedLines {
		// Combine marker indent with the original line's content (trimmed and re-indented)
		// This might double-indent if originalIndent wasn't just whitespace, be careful.
		// Let's just use markerIndent + trimmed line for simplicity.
		result.WriteString(markerIndent + strings.TrimSpace(line) + "\n")
	}

	// Add lines after the marker
	if injectIndex+1 < len(snippetLines) {
		// Ensure newline after injected code only if there are subsequent lines
		result.WriteString(strings.Join(snippetLines[injectIndex+1:], "\n"))
	}

	// DRAFT: Returns the modified snippet. Caller needs to handle integration.
	// TODO: Adapt snippet interface based on variables in injectedLines.
	// TODO: Modify originalContent to instantiate this modified snippet.
	return result.String(), nil
}

// MutateFile applies a random mutation strategy (InjectSnippet or AddCodeToSnippet)
func MutateFile(fileName string) error { // Removed snippets []string param
	// Read the original file content
	originalContent, err := utils.ReadFileContent(fileName)
	if err != nil {
		return fmt.Errorf("failed to read file %s: %v", fileName, err)
	}

	// Get a random snippet
	snippet, err := GetRandomSnippet()
	if err != nil {
		return fmt.Errorf("failed to get snippet for mutation: %v", err)
	}

	var mutatedContent string
	mutationType := utils.RandomInt(0, 1)

	if mutationType == 0 {
		// 1. Inject a snippet instance into the file
		fmt.Println("Attempting InjectSnippet mutation...")
		mutatedContent, err = InjectSnippet(originalContent, snippet)
		if err != nil {
			fmt.Printf("InjectSnippet failed: %v. Skipping mutation.\n", err)
			mutatedContent = originalContent // Keep original on error
		}
	} else {
		// 2. Add part of the code into a snippet's //INJECT marker
		fmt.Println("Attempting AddCodeToSnippet mutation...")
		modifiedSnippet, err := AddCodeToSnippet(originalContent, snippet)
		if err != nil {
			fmt.Printf("AddCodeToSnippet failed: %v. Skipping mutation.\n", err)
			mutatedContent = originalContent // Keep original on error
		} else {
			// --- Placeholder behavior for draft ---
			// Replace entire file content with the modified snippet.
			// This is NOT the final intended behavior. A real implementation
			// would replace the selected code block in the original file
			// with an instantiation of this modified snippet.
			fmt.Println("AddCodeToSnippet succeeded. Replacing content with modified snippet (Draft Behavior).")
			mutatedContent = modifiedSnippet
			// --- End Placeholder behavior ---
		}
	}

	// Write the mutated content back to the file
	err = utils.WriteFileContent(fileName, mutatedContent)
	if err != nil {
		return fmt.Errorf("failed to write mutated content to %s: %v", fileName, err)
	}
	fmt.Printf("Mutation applied to %s (Type: %d)\n", fileName, mutationType)
	return nil
}
