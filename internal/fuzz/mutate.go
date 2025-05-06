package fuzz

import (
	"errors"
	"fmt"
	"log"
	"math/rand"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strings"
	"time"

	"github.com/toby-bro/pfuzz/internal/verilog"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

var (
	modules    = []string{}
	seededRand = rand.New(rand.NewSource(time.Now().UnixNano()))
	classes    = map[string]string{}
)

type Snippet struct {
	Name      string
	Content   string
	Module    verilog.Module
	Depending []verilog.Class
}

func LoadSnippetModules() ([]string, map[string]string, error) {
	// Find the repository root by searching upwards for a .git directory
	cwd, err := os.Getwd()
	if err != nil {
		return nil, nil, fmt.Errorf("failed to get current working directory: %w", err)
	}

	repoRoot := ""
	dir := cwd
	for {
		// Check if .git exists in the current directory
		gitPath := filepath.Join(dir, ".git")
		stat, err := os.Stat(gitPath)
		if err == nil && stat.IsDir() {
			repoRoot = dir // Found the repository root
			break
		}
		// Handle errors other than "not found"
		if err != nil && !os.IsNotExist(err) {
			return nil, nil, fmt.Errorf("error checking for .git directory at %s: %w", gitPath, err)
		}

		// Move to the parent directory
		parentDir := filepath.Dir(dir)
		if parentDir == dir {
			// Reached the filesystem root without finding .git
			return nil, nil, fmt.Errorf(
				"failed to find repository root (.git directory) starting from %s",
				cwd,
			)
		}
		dir = parentDir
	}

	if repoRoot == "" {
		// Should not happen if the loop logic is correct, but handle defensively
		return nil, nil, errors.New("repository root could not be determined")
	}

	// Construct the path to the snippets directory relative to the repo root
	snippetsDir := filepath.Join(repoRoot, "snippets")

	// Check if the snippets directory exists
	if _, err := os.Stat(snippetsDir); os.IsNotExist(err) {
		return nil, nil, fmt.Errorf("snippets directory '%s' does not exist", snippetsDir)
	} else if err != nil {
		return nil, nil, fmt.Errorf("failed to access snippets directory '%s': %w", snippetsDir, err)
	}

	sourceFiles, err := filepath.Glob(filepath.Join(snippetsDir, "*.sv"))
	log.Printf("Loading snippets from directory: %s", snippetsDir)
	if err != nil {
		return nil, nil, err
	}

	allModules := make(map[string]string)
	allClasses := make(map[string]string)
	for _, snippetFile := range sourceFiles {
		modules, classes, err := verilog.ExtractDefinitions(snippetFile)
		if err != nil {
			return nil, nil, err
		}
		for name, content := range modules {
			allModules[name] = content
		}
		for name, content := range classes {
			allClasses[name] = content
		}
	}
	// Convert map to slice
	snippetList := make([]string, 0, len(allModules))
	for _, content := range allModules {
		snippetList = append(snippetList, content)
	}
	return snippetList, allClasses, nil
}

// returns the list of modules and the map of classes defined in the snippets directory
func GetSnippets() ([]string, map[string]string, error) {
	if len(modules) == 0 {
		var err error
		modules, classes, err = LoadSnippetModules()
		if err != nil {
			return nil, nil, fmt.Errorf("failed to load snippets: %v", err)
		}
	}
	return modules, classes, nil
}

// GetRandomSnippet returns a random snippet from the loaded module snippets.
func GetRandomSnippet() (string, error) {
	snippets, _, err := GetSnippets()
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
			Name:  fallbackName,
			Ports: []verilog.Port{}, // Assume no ports if parsing failed
			Body:  snippet,          // Keep original content for potential later use
		}
		// Note: Without parsed ports, instantiation will be empty `module_name instance_name ();`
	}
	if snippetModule == nil || snippetModule.Name == "" {
		return originalContent, errors.New("failed to identify module name in snippet")
	}

	originalLines := strings.Split(originalContent, "\n")
	instanceName := fmt.Sprintf("%s_inst_%d", snippetModule.Name, seededRand.Intn(10000))
	newDeclarations := []string{} // For adding internal logic declarations
	connections := []string{}
	usedOrigVars := make(map[string]bool)

	// 3. Find Insertion Point (logic remains the same)
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

	// 4. Identify Candidate Signals (logic remains the same)
	candidateSignals := make(map[string]verilog.Port) // Use Port struct for convenience
	// Add Ports
	for _, p := range originalModule.Ports {
		candidateSignals[p.Name] = p
	}
	// Add Internal Signals found before insertion point using Regex
	internalSignalRegex := regexp.MustCompile(
		`(?i)^\s*(wire|reg|logic)\s*(signed|unsigned)?\s*(\[[^\]]+\])?\s*([a-zA-Z_][\w,\s]*)\s*;`,
	)
	for i := 0; i < insertionLineIndex; i++ {
		line := strings.TrimSpace(originalLines[i])
		matches := internalSignalRegex.FindStringSubmatch(line)
		if len(matches) > 4 {
			sigType := verilog.GetPortType(strings.ToLower(matches[1]))
			isSigned := strings.ToLower(matches[2]) == "signed"
			widthStr := matches[3]
			width := 1
			if widthStr != "" {
				var high, low int
				if _, err := fmt.Sscanf(widthStr, "[%d:%d]", &high, &low); err == nil {
					width = high - low + 1
				} else if _, err := fmt.Sscanf(widthStr, "[%d]", &high); err == nil {
					width = high
				}
				if width <= 0 {
					width = 1
				}
			}

			names := strings.Split(matches[4], ",")
			for _, name := range names {
				trimmedName := strings.TrimSpace(name)
				if trimmedName != "" &&
					candidateSignals[trimmedName].Name == "" {
					candidateSignals[trimmedName] = verilog.Port{
						Name:      trimmedName,
						Direction: verilog.INTERNAL,
						Type:      sigType,
						Width:     width,
						IsSigned:  isSigned,
					}
				}
			}
		}
	}

	// 5. Determine Connections for Snippet Ports
	for _, snipPort := range snippetModule.Ports {
		signalName := ""
		foundMatch := false

		if snipPort.Direction == verilog.INPUT {
			possibleMatches := []string{}
			for name, origSig := range candidateSignals {
				isClockReset := strings.Contains(strings.ToLower(name), "clk") ||
					strings.Contains(strings.ToLower(name), "clock") ||
					strings.Contains(strings.ToLower(name), "rst") ||
					strings.Contains(strings.ToLower(name), "reset")

				compatible := true
				if snipPort.Width > 0 && origSig.Width > 0 && snipPort.Width != origSig.Width {
					compatible = false
				}
				if snipPort.IsSigned != origSig.IsSigned {
					compatible = false
				}

				if compatible {
					if isClockReset {
						if seededRand.Intn(10) < 2 {
							possibleMatches = append(possibleMatches, name)
						}
					} else {
						possibleMatches = append(possibleMatches, name)
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

			if !foundMatch {
				signalName = fmt.Sprintf(
					"inj_unconnected_%s_%d",
					strings.ToLower(snipPort.Name),
					seededRand.Intn(100),
				)
				fmt.Printf(
					"    No compatible signal found for snippet input '%s'. Declaring placeholder internal signal '%s'.\n",
					snipPort.Name,
					signalName,
				)
				widthStr := ""
				if snipPort.Width > 1 {
					widthStr = fmt.Sprintf("[%d:0] ", snipPort.Width-1)
				}
				signedStr := ""
				if snipPort.IsSigned {
					signedStr = "signed "
				}
				newDeclarations = append(
					newDeclarations,
					fmt.Sprintf("logic %s%s%s;", signedStr, widthStr, signalName),
				)
			}
			connections = append(connections, fmt.Sprintf(".%s(%s)", snipPort.Name, signalName))
		} else {
			possibleMatches := []string{}
			for name, origSig := range candidateSignals {
				compatible := true
				if snipPort.Width > 0 && origSig.Width > 0 && snipPort.Width != origSig.Width {
					compatible = false
				}
				if snipPort.IsSigned != origSig.IsSigned {
					compatible = false
				}
				isConnectableType := origSig.Direction == verilog.INTERNAL || origSig.Direction == verilog.OUTPUT
				if compatible && isConnectableType && !usedOrigVars[name] {
					possibleMatches = append(possibleMatches, name)
				}
			}

			if len(possibleMatches) > 0 {
				sort.SliceStable(possibleMatches, func(i, j int) bool {
					return candidateSignals[possibleMatches[i]].Direction == verilog.INTERNAL &&
						candidateSignals[possibleMatches[j]].Direction != verilog.INTERNAL
				})
				signalName = possibleMatches[0]
				usedOrigVars[signalName] = true
				fmt.Printf("    Connecting snippet output '%s' to existing signal '%s'\n", snipPort.Name, signalName)
				foundMatch = true
			}

			if !foundMatch {
				directionPrefix := "output"
				if snipPort.Direction == verilog.INOUT {
					directionPrefix = "inout"
					fmt.Printf("    Warning: Declaring new internal wire for INOUT port '%s'. May require manual connection logic.\n", snipPort.Name)
				}
				signalName = fmt.Sprintf("inj_%s_%s_%d", directionPrefix, strings.ToLower(snipPort.Name), seededRand.Intn(1000))

				fmt.Printf(
					"    No compatible internal signal found for snippet %s '%s'. Declaring internal signal '%s'.\n",
					directionPrefix,
					snipPort.Name,
					signalName,
				)

				widthStr := ""
				if snipPort.Width > 1 {
					widthStr = fmt.Sprintf("[%d:0] ", snipPort.Width-1)
				}
				signedStr := ""
				if snipPort.IsSigned {
					signedStr = "signed "
				}
				newDeclarations = append(newDeclarations, fmt.Sprintf("logic %s%s%s;", signedStr, widthStr, signalName))
			}
			connections = append(connections, fmt.Sprintf(".%s(%s)", snipPort.Name, signalName))
		}
	}

	// 6. Construct Instantiation String
	instantiation := ""
	if len(connections) > 0 {
		instantiation = fmt.Sprintf("%s %s (", snippetModule.Name, instanceName)
		instantiation += "\n"
		sort.SliceStable(connections, func(i, j int) bool {
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
		instantiation = fmt.Sprintf("%s %s ();", snippetModule.Name, instanceName)
	}

	// 7. Assemble Final Code
	var result strings.Builder

	result.WriteString(snippet)
	result.WriteString("\n\n")

	for i := 0; i < insertionLineIndex; i++ {
		result.WriteString(originalLines[i])
		result.WriteString("\n")
	}

	if len(newDeclarations) > 0 {
		result.WriteString(indent + "// Declarations for injected module instance\n")
		sort.Strings(newDeclarations)
		for _, decl := range newDeclarations {
			result.WriteString(indent + decl + "\n")
		}
		result.WriteString("\n")
	}

	result.WriteString(indent + "// Instantiation of injected module\n")
	result.WriteString(indent + instantiation + "\n\n")

	for i := insertionLineIndex; i < len(originalLines); i++ {
		result.WriteString(originalLines[i])
		if i < len(originalLines)-1 || len(strings.TrimSpace(originalLines[i])) > 0 {
			result.WriteString("\n")
		}
	}

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
		)
	}

	injectIndex := -1
	markerIndent := ""
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
		)
	}

	numLinesToInject := utils.RandomInt(1, 3)
	injectedLines := []string{}
	maxAttempts := 30
	attempts := 0
	skipLineRegex := regexp.MustCompile(
		`^\s*(?:\/\/|\/\*|\*\/|module|endmodule|input|output|inout|wire|reg|logic|parameter|localparam)\b`,
	)

	originalModule, origErr := verilog.ParseVerilogContent(
		[]byte(originalContent),
		"",
	)
	startLine, endLine := 0, len(originalLines)-1
	if origErr == nil && originalModule != nil {
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
		idx := utils.RandomInt(startLine, endLine)
		if idx >= len(originalLines) {
			continue
		}

		line := originalLines[idx]
		trimmedLine := strings.TrimSpace(line)

		if trimmedLine != "" && !skipLineRegex.MatchString(line) {
			if trimmedLine != "end" && trimmedLine != "begin" &&
				!strings.HasPrefix(trimmedLine, "end ") {
				injectedLines = append(injectedLines, line)
			}
		}
	}

	if len(injectedLines) == 0 {
		fmt.Println("    No suitable lines found to inject. Removing //INJECT marker.")
		return strings.Join(
			append(snippetLines[:injectIndex], snippetLines[injectIndex+1:]...),
			"\n",
		), nil
	}

	var result strings.Builder
	result.WriteString(strings.Join(snippetLines[:injectIndex], "\n"))
	if injectIndex > 0 {
		result.WriteString("\n")
	}

	fmt.Printf("    Injecting %d lines into snippet...\n", len(injectedLines))
	for _, line := range injectedLines {
		result.WriteString(markerIndent + strings.TrimSpace(line) + "\n")
	}

	if injectIndex+1 < len(snippetLines) {
		result.WriteString(strings.Join(snippetLines[injectIndex+1:], "\n"))
	}

	return result.String(), nil
}

// MutateFile applies a random mutation strategy (InjectSnippet or AddCodeToSnippet)
func MutateFile(fileName string) error {
	originalContent, err := utils.ReadFileContent(fileName)
	if err != nil {
		return fmt.Errorf("failed to read file %s: %v", fileName, err)
	}

	snippet, err := GetRandomSnippet()
	if err != nil {
		return fmt.Errorf("failed to get snippet for mutation: %v", err)
	}

	var mutatedContent string
	mutationType := 0

	if mutationType == 0 {
		fmt.Println("Attempting InjectSnippet mutation...")
		mutatedContent, err = InjectSnippet(originalContent, snippet)
		if err != nil {
			fmt.Printf("InjectSnippet failed: %v. Skipping mutation.\n", err)
			return fmt.Errorf("InjectSnippet failed: %w", err)
		}
	} else {
		mutatedContent = originalContent
	}

	err = utils.WriteFileContent(fileName, mutatedContent)
	if err != nil {
		return fmt.Errorf("failed to write mutated content to %s: %v", fileName, err)
	}
	fmt.Printf("Mutation applied to %s (Type: %d)\n", fileName, mutationType)
	return nil
}
