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
	fileName := filepath.Base(filePath)
	moduleName := ""

	lines := strings.Split(fileContent, "\n")
	allModules := make(map[string]string)
	moduleContent := []string{}

	for _, line := range lines {
		if strings.HasPrefix(line, "module") {
			moduleName = fileName + strings.TrimSpace(strings.Split(line, " ")[1])
			moduleContent = append(moduleContent, line)
		} else if strings.HasPrefix(line, "endmodule") {
			moduleContent = append(moduleContent, line)

			if moduleName != "" {
				allModules[moduleName] = strings.Join(moduleContent, "\n")
				moduleContent = []string{}
				moduleName = ""
			}
		} else if moduleName != "" {
			moduleContent = append(moduleContent, line)
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

// parseVerilogString parses module information from a string content.
// NOTE: This is a simplified version using regex, not the full parser logic.
// It primarily extracts module name and ports from the header.
func parseVerilogString(content string) (*verilog.Module, error) {
	module := &verilog.Module{
		Name:    "",
		Ports:   []verilog.Port{},
		Content: content,
	}

	// Find module declaration and port list
	// module my_module ( input logic clk, output logic [7:0] data );
	moduleRegex := regexp.MustCompile(`module\s+(\w+)\s*\(([\s\S]*?)\);`)
	moduleMatches := moduleRegex.FindStringSubmatch(content)

	if len(moduleMatches) < 3 {
		return nil, errors.New("could not find module definition")
	}
	module.Name = moduleMatches[1]
	portList := moduleMatches[2]

	// Basic ANSI port parsing from header
	ansiPortRegex := regexp.MustCompile(
		`^\s*(input|output|inout)?\s*` + // Optional direction (1)
			`(logic|reg|wire|bit|int)?\s*` + // Optional type (2) - simplified types
			`(\[\s*[\w\-\+\:\s]+\s*\])?\s*` + // Optional range (3)
			`(\w+)\s*$`, // Port name (4)
	)

	portDeclarations := strings.Split(portList, ",")
	for _, decl := range portDeclarations {
		decl = strings.TrimSpace(decl)
		if decl == "" {
			continue
		}

		matches := ansiPortRegex.FindStringSubmatch(decl)
		if len(matches) >= 5 {
			directionStr := strings.TrimSpace(matches[1])
			portType := strings.TrimSpace(matches[2])
			rangeStr := strings.TrimSpace(matches[3])
			portName := strings.TrimSpace(matches[4])

			if portType == "" {
				portType = "logic"
			} // Default

			var direction verilog.PortDirection
			switch directionStr {
			case "input":
				direction = verilog.INPUT
			case "output":
				direction = verilog.OUTPUT
			case "inout":
				direction = verilog.INOUT
			default:
				direction = verilog.INPUT // Default if missing
			}

			width := 1
			if rangeStr != "" {
				// Very basic check for multi-bit
				if strings.Contains(rangeStr, ":") {
					// Attempt to parse simple [N:0]
					simpleRangeRegex := regexp.MustCompile(`\[\s*(\d+)\s*:\s*0\s*\]`)
					if wMatches := simpleRangeRegex.FindStringSubmatch(rangeStr); len(
						wMatches,
					) > 1 {
						fmt.Sscanf(wMatches[1], "%d", &width)
						width++ // width = N+1
					} else {
						width = 8 // Default guess for multi-bit
					}
				}
			}

			module.Ports = append(module.Ports, verilog.Port{
				Name: portName, Direction: direction, Type: portType, Width: width,
			})
		} else {
			// Fallback for simple names (assume 1-bit logic input)
			simpleNameRegex := regexp.MustCompile(`^\s*(\w+)\s*$`)
			if nameMatches := simpleNameRegex.FindStringSubmatch(decl); len(nameMatches) > 1 {
				module.Ports = append(module.Ports, verilog.Port{
					Name: nameMatches[1], Direction: verilog.INPUT, Type: "logic", Width: 1,
				})
			}
		}
	}
	if len(module.Ports) == 0 {
		return nil, errors.New("could not parse any ports from module header")
	}
	return module, nil
}

// InjectSnippet attempts to inject a snippet module instantiation into the original content.
// Draft version: Uses simplified parsing and placeholder connections.
func InjectSnippet(originalContent, snippet string) (string, error) {
	origLines := strings.Split(originalContent, "\n")
	if len(origLines) <= 1 {
		return originalContent, errors.New("original content too short to inject")
	}

	// Parse the snippet
	snippetModule, err := parseVerilogString(snippet)
	if err != nil {
		return originalContent, fmt.Errorf("failed to parse snippet: %v", err)
	}

	// --- Draft Instantiation ---
	// TODO: Parse originalContent properly to find matching signals.
	// For now, create placeholder signal names based on snippet port names.
	instanceName := fmt.Sprintf("%s_inst_%d", snippetModule.Name, seededRand.Intn(10000))
	instantiation := fmt.Sprintf("%s %s (", snippetModule.Name, instanceName)
	connections := []string{}
	newDeclarations := []string{} // Wires needed for snippet outputs

	for _, port := range snippetModule.Ports {
		// Basic renaming: replace GGG prefix if present
		signalName := port.Name
		if strings.HasPrefix(signalName, "GGG") {
			signalName = "inj_" + strings.ToLower(
				port.Name[3:],
			) + fmt.Sprintf(
				"_%d",
				seededRand.Intn(100),
			)
		} else {
			signalName = "inj_" + strings.ToLower(port.Name) + fmt.Sprintf("_%d", seededRand.Intn(100))
		}

		connections = append(connections, fmt.Sprintf(".%s(%s)", port.Name, signalName))

		// If it's an output, declare a wire for it (simplistic)
		if port.Direction == verilog.OUTPUT {
			widthStr := ""
			if port.Width > 1 {
				widthStr = fmt.Sprintf("[%d:0] ", port.Width-1)
			}
			newDeclarations = append(
				newDeclarations,
				fmt.Sprintf("logic %s%s;", widthStr, signalName),
			)
		}
		// TODO: Need to find matching *input* signals in originalContent or declare them too?
		// For now, assume inputs magically exist or are driven elsewhere.
	}
	instantiation += strings.Join(connections, ", ") + ");"
	// --- End Draft Instantiation ---

	// Find insertion point: Just before the first `endmodule`
	insertionPoint := -1
	for i := len(origLines) - 1; i >= 0; i-- {
		if strings.HasPrefix(strings.TrimSpace(origLines[i]), "endmodule") {
			insertionPoint = i
			break
		}
	}
	if insertionPoint == -1 {
		insertionPoint = len(origLines) - 1 // Fallback: end of file
	}

	// Inject the snippet module definition at the beginning
	// and the instantiation + declarations at the insertion point.
	var result strings.Builder
	result.WriteString(snippet) // Add the snippet module definition
	result.WriteString("\n\n")

	for i, line := range origLines {
		if i == insertionPoint {
			// Add new wire declarations needed for snippet outputs
			for _, decl := range newDeclarations {
				result.WriteString("    " + decl + "\n") // Assuming inside a module, add indent
			}
			result.WriteString("    " + instantiation + "\n") // Add the instantiation
		}
		result.WriteString(line)
		result.WriteString("\n")
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
		) // Return original snippet on error
	}

	// Find the //INJECT marker
	injectIndex := -1
	indent := ""
	indentRegex := regexp.MustCompile(`^(\s*)`)
	for i, line := range snippetLines {
		if strings.Contains(line, "//INJECT") {
			injectIndex = i
			if matches := indentRegex.FindStringSubmatch(line); len(matches) > 1 {
				indent = matches[1]
			}
			break
		}
	}

	if injectIndex == -1 {
		return snippet, errors.New(
			"snippet does not contain //INJECT marker",
		) // Return original snippet
	}

	// Select 1 to 3 random lines from the original content (excluding module/endmodule/comments)
	numLinesToInject := utils.RandomInt(1, 3)
	injectedLines := []string{}
	maxAttempts := 20
	attempts := 0
	validLineRegex := regexp.MustCompile(`^\s*(?:\/\/|module|endmodule|\/\*|\*\/)`) // Lines to skip
	for len(injectedLines) < numLinesToInject && attempts < maxAttempts {
		attempts++
		idx := utils.RandomInt(0, len(originalLines)-1)
		trimmedLine := strings.TrimSpace(originalLines[idx])

		if trimmedLine != "" && !validLineRegex.MatchString(originalLines[idx]) {
			injectedLines = append(injectedLines, originalLines[idx])
		}
	}

	if len(injectedLines) == 0 {
		// If no lines selected, just remove the marker
		return strings.Join(
			append(snippetLines[:injectIndex], snippetLines[injectIndex+1:]...),
			"\n",
		), nil
	}

	// Replace the //INJECT line with the selected lines
	var result strings.Builder
	result.WriteString(strings.Join(snippetLines[:injectIndex], "\n"))
	result.WriteString("\n") // Ensure newline before injected code

	for _, line := range injectedLines {
		// Try to preserve relative indentation from original line, plus snippet indent
		originalIndent := ""
		if matches := indentRegex.FindStringSubmatch(line); len(matches) > 1 {
			originalIndent = matches[1]
		}
		result.WriteString(indent + originalIndent + strings.TrimSpace(line) + "\n")
	}
	result.WriteString(strings.Join(snippetLines[injectIndex+1:], "\n"))

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
