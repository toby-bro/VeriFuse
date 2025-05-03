package fuzz

import (
	"errors"
	"fmt"
	"math/rand"
	"path/filepath"
	"regexp"
	"sort"
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
// It analyzes the original module to find a suitable insertion point and connect snippet ports.
func InjectSnippet(originalContent string, snippet string) (string, error) { // nolint:gocyclo
	// 1. Parse Original Content
	originalModule, err := verilog.ParseVerilogContent([]byte(originalContent), "")
	if err != nil {
		return originalContent, fmt.Errorf("failed to parse original content: %v", err)
	}
	if originalModule == nil || originalModule.Name == "" {
		return originalContent, errors.New("could not identify module in original content")
	}

	// 2. Parse Snippet Content
	snippetModule, err := verilog.ParseVerilogContent([]byte(snippet), "")
	if err != nil {
		// Fallback parsing for snippet name if full parse fails
		generalModuleRegex := regexp.MustCompile(`(?m)^\s*module\s+(\w+)`) // Added (?m)^
		matches := generalModuleRegex.FindStringSubmatch(snippet)
		fallbackName := "unknown_snippet"
		if len(matches) > 1 {
			fallbackName = matches[1]
		}
		fmt.Printf(
			"Warning: Failed to fully parse snippet: %v. Proceeding with fallback name '%s' and assuming no ports.\n",
			err,
			fallbackName,
		)
		// Create a minimal module structure for the fallback
		snippetModule = &verilog.Module{
			Name:    fallbackName,
			Ports:   []verilog.Port{}, // Assume no ports if parsing failed
			Content: snippet,          // Keep original content for potential later use
		}
		// Note: Without parsed ports, instantiation will be empty `module_name instance_name ();`
	}
	if snippetModule == nil || snippetModule.Name == "" {
		return originalContent, errors.New("failed to identify module name in snippet")
	}

	// --- Start Refactored Logic ---

	originalLines := strings.Split(originalContent, "\n")
	instanceName := fmt.Sprintf("%s_inst_%d", snippetModule.Name, seededRand.Intn(10000))
	newDeclarations := []string{}
	connections := []string{}
	usedOrigVars := make(map[string]bool) // Track original vars used for snippet outputs

	// 3. Find Insertion Point (Moved earlier)
	// Strategy: Insert after the last declaration (port, wire, reg, logic, parameter, etc.)
	lastDeclarationLine := -1
	declarationRegex := regexp.MustCompile(
		`(?i)^\s*(input|output|inout|wire|reg|logic|parameter|localparam|integer|genvar)\b`,
	)
	moduleHeaderEndRegex := regexp.MustCompile(`\)\s*;`) // Matches the end of port list

	moduleHeaderEndLine := -1
	for i, line := range originalLines {
		// Look for module definition line to start search for header end
		if strings.HasPrefix(strings.TrimSpace(line), "module ") {
			for j := i + 1; j < len(originalLines); j++ {
				if moduleHeaderEndRegex.MatchString(originalLines[j]) {
					moduleHeaderEndLine = j
					break
				}
				// Stop searching for header end if we hit procedural blocks or endmodule early
				trimmedJLine := strings.TrimSpace(originalLines[j])
				if strings.HasPrefix(trimmedJLine, "always") ||
					strings.HasPrefix(trimmedJLine, "assign") ||
					strings.HasPrefix(trimmedJLine, "initial") ||
					strings.HasPrefix(trimmedJLine, "generate") ||
					strings.HasPrefix(trimmedJLine, "endmodule") {
					break
				}
			}
			break // Stop after finding the first module line
		}
	}

	if moduleHeaderEndLine == -1 {
		// Fallback: Assume first few lines might be header if regex fails
		moduleHeaderEndLine = utils.Min(5, len(originalLines)/4) // Avoid going too far
		fmt.Println(
			"Warning: Could not reliably detect module header end ';'. Using fallback line number:",
			moduleHeaderEndLine,
		)
	}

	// Search for declarations *after* the estimated header end
	searchStartLine := moduleHeaderEndLine + 1
	if searchStartLine >= len(originalLines) {
		searchStartLine = len(originalLines) - 1 // Ensure start is within bounds
	}
	for i := searchStartLine; i < len(originalLines); i++ {
		trimmedLine := strings.TrimSpace(originalLines[i])
		// Check if it's a declaration
		if declarationRegex.MatchString(trimmedLine) {
			lastDeclarationLine = i
		}
		// Stop searching if we hit procedural blocks, assignments, generate, or endmodule
		if strings.HasPrefix(trimmedLine, "always") ||
			strings.HasPrefix(trimmedLine, "assign") ||
			strings.HasPrefix(trimmedLine, "initial") ||
			strings.HasPrefix(trimmedLine, "generate") ||
			strings.HasPrefix(trimmedLine, "endmodule") ||
			strings.Contains(trimmedLine, "=") { // Also stop on assignments
			break
		}
	}

	var insertionLineIndex int
	if lastDeclarationLine != -1 {
		insertionLineIndex = lastDeclarationLine + 1 // Insert on the line after the last declaration found
	} else {
		// Fallback: Insert after the module header end line if no declarations found
		insertionLineIndex = moduleHeaderEndLine + 1
		fmt.Println("Warning: Could not find declarations after module header. Inserting after header.")
	}

	// Ensure insertion index is within bounds and before endmodule if possible
	endModuleLine := -1
	for i := len(originalLines) - 1; i >= 0; i-- {
		if strings.Contains(originalLines[i], "endmodule") {
			endModuleLine = i
			break
		}
	}
	if endModuleLine != -1 && insertionLineIndex >= endModuleLine {
		insertionLineIndex = endModuleLine // Insert before endmodule if calculated index is too late
	}
	if insertionLineIndex >= len(originalLines) {
		insertionLineIndex = len(originalLines) // Absolute fallback: append (should be rare)
	}
	if insertionLineIndex < 0 {
		return "", errors.New("invalid insertion line index calculated")
	}

	// Determine indentation from the line *before* the insertion point
	indent := "    " // Default indent
	if insertionLineIndex > 0 && insertionLineIndex <= len(originalLines) {
		// Find the previous non-empty, non-comment line to determine indent
		searchIndentLine := insertionLineIndex - 1
		for searchIndentLine > 0 {
			prevLineTrimmed := strings.TrimSpace(originalLines[searchIndentLine])
			if prevLineTrimmed != "" && !strings.HasPrefix(prevLineTrimmed, "//") &&
				!strings.HasPrefix(prevLineTrimmed, "/*") {
				break
			}
			searchIndentLine--
		}
		if searchIndentLine >= 0 {
			lineBefore := originalLines[searchIndentLine]
			indentRegex := regexp.MustCompile(`^(\s*)`)
			if matches := indentRegex.FindStringSubmatch(lineBefore); len(matches) > 1 {
				indent = matches[1] // Use existing indent
			}
		}
	}

	// 4. Identify Candidate Signals in Original Module (Ports + Internal Signals before insertion)
	candidateSignals := make(map[string]verilog.Port) // Use Port struct for convenience
	// Add Ports
	for _, p := range originalModule.Ports {
		candidateSignals[p.Name] = p
	}
	// Add Internal Signals found before insertion point using Regex
	// Basic Regex: `^\s*(wire|reg|logic)\s*(signed|unsigned)?\s*(\[[^\]]+\])?\s*([\w,\s]+)\s*;`
	// Simplified Regex focusing on name:
	internalSignalRegex := regexp.MustCompile(
		`(?i)^\s*(wire|reg|logic)\s*(signed|unsigned)?\s*(\[[^\]]+\])?\s*([a-zA-Z_][\w,\s]*)\s*;`,
	)
	for i := 0; i < insertionLineIndex; i++ {
		line := strings.TrimSpace(originalLines[i])
		matches := internalSignalRegex.FindStringSubmatch(line)
		// matches[0] = full match
		// matches[1] = type (wire/reg/logic)
		// matches[2] = signed/unsigned (optional)
		// matches[3] = width (optional) e.g. [7:0]
		// matches[4] = signal names (comma-separated potentially) e.g. sig_a, sig_b
		if len(matches) > 4 {
			sigType := strings.ToLower(matches[1])
			if sigType == "" {
				sigType = "logic"
			} // Default if regex somehow misses it
			isSigned := strings.ToLower(matches[2]) == "signed"
			widthStr := matches[3]
			width := 1 // Default width
			if widthStr != "" {
				// Basic width parsing (can be improved for complex ranges)
				var high, low int
				if _, err := fmt.Sscanf(widthStr, "[%d:%d]", &high, &low); err == nil {
					width = high - low + 1
				} else if _, err := fmt.Sscanf(widthStr, "[%d]", &high); err == nil {
					width = high // Single index often implies width high+1 if low is 0? Assume width 1 for simplicity here.
				}
				if width <= 0 {
					width = 1
				} // Ensure positive width
			}

			// Split comma-separated names
			names := strings.Split(matches[4], ",")
			for _, name := range names {
				trimmedName := strings.TrimSpace(name)
				if trimmedName != "" &&
					candidateSignals[trimmedName].Name == "" { // Avoid overwriting ports/earlier declarations
					candidateSignals[trimmedName] = verilog.Port{
						Name:      trimmedName,
						Direction: verilog.INTERNAL, // Mark as internal
						Type:      sigType,
						Width:     width,
						IsSigned:  isSigned,
					}
					// fmt.Printf("    Found internal signal: %s (Type: %s, Width: %d, Signed: %t)\n", trimmedName, sigType, width, isSigned)
				}
			}
		}
	}

	// 5. Determine Connections for Snippet Ports (Renumbered step)
	for _, snipPort := range snippetModule.Ports {
		signalName := ""
		foundMatch := false

		if snipPort.Direction == verilog.INPUT {
			// Find compatible signal in original module (ports or internal signals)
			possibleMatches := []string{}
			for name, origSig := range candidateSignals {
				// Basic compatibility check (can be enhanced)
				isClockReset := strings.Contains(strings.ToLower(name), "clk") ||
					strings.Contains(strings.ToLower(name), "clock") ||
					strings.Contains(strings.ToLower(name), "rst") ||
					strings.Contains(strings.ToLower(name), "reset")

				// Simple type/width check (if types are parsed)
				compatible := true // Assume compatible for now if types/widths are missing/mismatch
				// TODO: Refine compatibility check - maybe allow different types (wire/logic/reg) but enforce width/signedness?
				// if snipPort.Type != "" && origSig.Type != "" && snipPort.Type != origSig.Type {
				// 	compatible = false // Relaxing type check for now
				// }
				if snipPort.Width > 0 && origSig.Width > 0 && snipPort.Width != origSig.Width {
					compatible = false
				}
				if snipPort.IsSigned != origSig.IsSigned {
					compatible = false
				}

				if compatible {
					// Add to possible matches, giving lower priority to clock/reset
					if isClockReset {
						if seededRand.Intn(10) < 2 { // ~20% chance to consider clk/rst
							possibleMatches = append(possibleMatches, name)
						}
					} else {
						possibleMatches = append(possibleMatches, name) // Higher chance for others
					}
				}
			}

			if len(possibleMatches) > 0 {
				signalName = possibleMatches[seededRand.Intn(len(possibleMatches))]
				fmt.Printf(
					"    Matching snippet input '%s' to original signal '%s'\n",
					snipPort.Name,
					signalName,
				)
				foundMatch = true
			}

			// If no compatible signal found, generate placeholder
			if !foundMatch {
				signalName = fmt.Sprintf(
					"inj_unconnected_%s_%d",
					strings.ToLower(snipPort.Name),
					seededRand.Intn(100),
				)
				fmt.Printf(
					"    No compatible signal found for snippet input '%s'. Using placeholder '%s'.\n",
					snipPort.Name,
					signalName,
				)
				// Consider declaring this placeholder? For now, leave unconnected.
			}
			connections = append(connections, fmt.Sprintf(".%s(%s)", snipPort.Name, signalName))
		} else { // OUTPUT or INOUT
			// Try to connect to an existing, compatible, unused signal declared *before* insertion point
			possibleMatches := []string{}
			for name, origSig := range candidateSignals {
				// Check compatibility (Width, Signedness) - Type check relaxed
				compatible := true
				if snipPort.Width > 0 && origSig.Width > 0 && snipPort.Width != origSig.Width {
					compatible = false
				}
				if snipPort.IsSigned != origSig.IsSigned {
					compatible = false
				}
				// Must be an internal signal (wire/reg/logic) or an output port, and not already used by another snippet output
				isConnectableType := origSig.Direction == verilog.INTERNAL || origSig.Direction == verilog.OUTPUT
				if compatible && isConnectableType && !usedOrigVars[name] {
					possibleMatches = append(possibleMatches, name)
				}
			}

			if len(possibleMatches) > 0 {
				// Prefer internal signals over output ports if available
				sort.SliceStable(possibleMatches, func(i, j int) bool {
					return candidateSignals[possibleMatches[i]].Direction == verilog.INTERNAL &&
						candidateSignals[possibleMatches[j]].Direction != verilog.INTERNAL
				})
				signalName = possibleMatches[0] // Choose the best match (potentially an internal signal)
				usedOrigVars[signalName] = true // Mark this original signal as used
				fmt.Printf("    Connecting snippet output '%s' to existing signal '%s'\n", snipPort.Name, signalName)
				foundMatch = true
			}

			// If no suitable existing signal found, declare a new one
			if !foundMatch {
				directionPrefix := "output"
				if snipPort.Direction == verilog.INOUT {
					directionPrefix = "inout"
					// Note: Connecting INOUT to a newly declared wire might require
					// additional logic (e.g., assigns) depending on how it's used.
					// This simplified approach might not be sufficient for all INOUT cases.
					fmt.Printf("    Warning: Declaring new wire for INOUT port '%s'. May require manual connection logic.\n", snipPort.Name)
				}
				signalName = fmt.Sprintf("inj_%s_%s_%d", directionPrefix, strings.ToLower(snipPort.Name), seededRand.Intn(1000))

				// Generate declaration for this internal signal
				widthStr := ""
				if snipPort.Width > 1 {
					widthStr = fmt.Sprintf("[%d:0] ", snipPort.Width-1)
				}
				signedStr := ""
				if snipPort.IsSigned {
					signedStr = "signed "
				}

				// Use 'logic' as a generally safe default for internal signals
				newDeclarations = append(newDeclarations, fmt.Sprintf("logic %s%s%s;", signedStr, widthStr, signalName))
				fmt.Printf("    Declaring internal signal '%s' for snippet %s '%s'\n", signalName, directionPrefix, snipPort.Name)
			}
			connections = append(connections, fmt.Sprintf(".%s(%s)", snipPort.Name, signalName))
		}
	}

	// 6. Construct Instantiation String
	// ... (rest of the function remains the same as previous version) ...
	instantiation := ""
	if len(connections) > 0 {
		instantiation = fmt.Sprintf("%s %s (", snippetModule.Name, instanceName)
		instantiation += "\n"
		// Sort connections alphabetically by port name for consistency
		sort.SliceStable(connections, func(i, j int) bool {
			// Extract port name between "." and "("
			portNameI := connections[i][1:strings.Index(connections[i], "(")]
			portNameJ := connections[j][1:strings.Index(connections[j], "(")]
			return portNameI < portNameJ
		})
		for i, conn := range connections {
			instantiation += indent + "    " + conn
			if i < len(connections)-1 {
				instantiation += ","
			}
			instantiation += "\n"
		}
		instantiation += indent + ");"
	} else {
		// Handle case with no ports (e.g., snippet parse failed)
		instantiation = fmt.Sprintf("%s %s ();", snippetModule.Name, instanceName)
	}

	// 7. Assemble Final Code
	var result strings.Builder

	// Add snippet module definition *before* the original module
	result.WriteString(snippet)
	result.WriteString("\n\n")

	// Write original lines up to the insertion point
	for i := 0; i < insertionLineIndex; i++ {
		result.WriteString(originalLines[i])
		result.WriteString("\n")
	}

	// Add new declarations (indented)
	if len(newDeclarations) > 0 {
		result.WriteString(indent + "// Declarations for injected module instance\n")
		sort.Strings(newDeclarations) // Keep declarations sorted for consistency
		for _, decl := range newDeclarations {
			result.WriteString(indent + decl + "\n")
		}
		result.WriteString("\n") // Add a blank line after declarations
	}

	// Add the instantiation (indented)
	result.WriteString(indent + "// Instantiation of injected module\n")
	result.WriteString(indent + instantiation + "\n\n") // Add blank line after instantiation

	// Write remaining original lines
	for i := insertionLineIndex; i < len(originalLines); i++ {
		result.WriteString(originalLines[i])
		// Add newline unless it's the very last line and potentially empty
		if i < len(originalLines)-1 || len(strings.TrimSpace(originalLines[i])) > 0 {
			result.WriteString("\n")
		}
	}

	// --- End Refactored Logic ---

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
	// mutationType := utils.RandomInt(0, 1) // Keep both mutations for now
	mutationType := 0 // Force InjectSnippet for testing the refactor

	if mutationType == 0 {
		// 1. Inject a snippet instance into the file
		fmt.Println("Attempting InjectSnippet mutation...")
		mutatedContent, err = InjectSnippet(originalContent, snippet)
		if err != nil {
			fmt.Printf("InjectSnippet failed: %v. Skipping mutation.\n", err)
			// Return error instead of writing original content back
			return fmt.Errorf("InjectSnippet failed: %w", err)
			// mutatedContent = originalContent // Keep original on error
		}
	} else {
		// 2. Add part of the code into a snippet's //INJECT marker
		fmt.Println("Attempting AddCodeToSnippet mutation...")
		modifiedSnippet, err := AddCodeToSnippet(originalContent, snippet)
		if err != nil {
			fmt.Printf("AddCodeToSnippet failed: %v. Skipping mutation.\n", err)
			// Return error instead of writing original content back
			return fmt.Errorf("AddCodeToSnippet failed: %w", err)
			// mutatedContent = originalContent // Keep original on error
		}
		// --- Placeholder behavior for draft ---
		// This mutation type still needs refinement to integrate properly.
		// For now, it replaces the whole file which is usually not desired.
		fmt.Println("AddCodeToSnippet succeeded. Replacing content with modified snippet (Draft Behavior).")
		mutatedContent = modifiedSnippet
		// --- End Placeholder behavior ---
	}

	// Write the mutated content back to the file only if mutation succeeded
	err = utils.WriteFileContent(fileName, mutatedContent)
	if err != nil {
		return fmt.Errorf("failed to write mutated content to %s: %v", fileName, err)
	}
	fmt.Printf("Mutation applied to %s (Type: %d)\n", fileName, mutationType)
	return nil
}
