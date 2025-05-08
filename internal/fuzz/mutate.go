package fuzz

import (
	"errors"
	"fmt"
	"log"
	"math/rand"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"time"

	"github.com/toby-bro/pfuzz/internal/verilog"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

var (
	seededRand   = rand.New(rand.NewSource(time.Now().UnixNano()))
	snippets     = []*Snippet{}
	verilogFiles = []*verilog.VerilogFile{}
)

type Snippet struct {
	Name       string
	Module     *verilog.Module
	ParentFile *verilog.VerilogFile
}

func findSnippetFiles() ([]string, error) {
	repoRoot, err := utils.LocateRepoRoot()
	if err != nil || repoRoot == "" {
		return nil, fmt.Errorf("failed to find repository root: %w", err)
	}

	snippetsDir := filepath.Join(repoRoot, "snippets")

	if _, err := os.Stat(snippetsDir); os.IsNotExist(err) {
		return nil, fmt.Errorf("snippets directory '%s' does not exist", snippetsDir)
	} else if err != nil {
		return nil, fmt.Errorf("failed to access snippets directory '%s': %w", snippetsDir, err)
	}

	sourceFiles, err := filepath.Glob(filepath.Join(snippetsDir, "*.sv"))
	log.Printf("Loading snippets from directory: %s", snippetsDir)
	if err != nil {
		return nil, err
	}
	return sourceFiles, nil
}

func loadSnippets() error {
	sourceFiles, err := findSnippetFiles()
	if err != nil {
		return fmt.Errorf("failed to find snippets: %v", err)
	}
	for _, snippetFile := range sourceFiles {
		fileContent, err := utils.ReadFileContent(snippetFile)
		if err != nil {
			return fmt.Errorf("failed to read snippet file %s: %v", snippetFile, err)
		}
		verilogFile, err := verilog.ParseVerilog(fileContent)
		if err != nil || verilogFile == nil {
			return err
		}
		for _, module := range verilogFile.Modules {
			if module.Name == "" {
				return fmt.Errorf("module name is empty in file %s", snippetFile)
			}
			snippets = append(snippets, &Snippet{
				Name:       module.Name,
				Module:     module,
				ParentFile: verilogFile,
			})
			verilogFiles = append(verilogFiles, verilogFile)
		}
	}
	return nil
}

func getSnippets() ([]*Snippet, []*verilog.VerilogFile, error) {
	if len(snippets) == 0 {
		err := loadSnippets()
		if err != nil {
			return nil, nil, fmt.Errorf("failed to load snippets: %v", err)
		}
	}
	return snippets, verilogFiles, nil
}

func getRandomSnippet() (*Snippet, error) {
	snippets, _, err := getSnippets()
	if err != nil {
		return nil, fmt.Errorf("failed to get snippets: %v", err)
	}
	if len(snippets) == 0 {
		return nil, errors.New("no snippets available")
	}
	randomIndex := utils.RandomInt(0, len(snippets)-1)
	return snippets[randomIndex], nil
}

func injectSnippetInModule(module *verilog.Module, snippet *Snippet) (string, error) {
	variables, err := verilog.ParseVariables(snippet.ParentFile, module.Body)
	if err != nil {
		return "", fmt.Errorf("failed to extract variables from module: %v", err)
	}

	portConnections, newSignalDeclarations, err := matchVariablesToSnippetPorts(
		module,
		snippet,
		variables,
	)
	if err != nil {
		return "", fmt.Errorf("failed to match variables to snippet ports: %v", err)
	}

	err = ensureOutputPortForSnippet(module, snippet, portConnections, newSignalDeclarations)
	if err != nil {
		return "", fmt.Errorf("failed to ensure output port for snippet: %v", err)
	}

	instantiation := generateSnippetInstantiation(snippet, portConnections)

	mutatedContent, err := insertSnippetIntoModule(module, instantiation, newSignalDeclarations)
	if err != nil {
		return "", fmt.Errorf("failed to insert snippet into module: %v", err)
	}

	return mutatedContent, nil
}

func matchVariablesToSnippetPorts(
	module *verilog.Module,
	snippet *Snippet,
	variables []*verilog.Variable,
) (map[string]string, []verilog.Port, error) {
	portConnections := make(map[string]string)
	newDeclarations := []verilog.Port{}

	usedInternalVars := make(map[string]bool)      // For variables from module.Body
	usedModuleInputPorts := make(map[string]bool)  // For module.Ports with direction INPUT
	usedModuleOutputPorts := make(map[string]bool) // For module.Ports with direction OUTPUT

	for _, port := range snippet.Module.Ports {
		foundMatch := false

		if port.Direction == verilog.INPUT {
			// 1. Try to match with an unused internal variable from the module body
			matchedVar := findMatchingVariable(port, variables, usedInternalVars)
			if matchedVar != nil {
				portConnections[port.Name] = matchedVar.Name
				usedInternalVars[matchedVar.Name] = true
				foundMatch = true
			}

			// 2. If no internal variable, try to match with an unused module input port
			if !foundMatch {
				for _, modulePort := range module.Ports {
					if modulePort.Direction == verilog.INPUT &&
						modulePort.Type == port.Type &&
						modulePort.Width == port.Width &&
						!usedModuleInputPorts[modulePort.Name] {
						portConnections[port.Name] = modulePort.Name
						usedModuleInputPorts[modulePort.Name] = true
						foundMatch = true
						break
					}
				}
			}
		} else if port.Direction == verilog.OUTPUT {
			// 1. Try to match with an unused internal variable (if it can be driven)
			//    or an existing module output port that ParseVariables might have picked up.
			//    For simplicity, we assume any compatible internal var can be connected.
			matchedVar := findMatchingVariable(port, variables, usedInternalVars)
			if matchedVar != nil {
				portConnections[port.Name] = matchedVar.Name
				usedInternalVars[matchedVar.Name] = true
				foundMatch = true
			}

			// 2. If no internal variable, try to match with an unused module output port
			if !foundMatch {
				for _, modulePort := range module.Ports {
					if modulePort.Direction == verilog.OUTPUT &&
						modulePort.Type == port.Type &&
						modulePort.Width == port.Width &&
						!usedModuleOutputPorts[modulePort.Name] {
						portConnections[port.Name] = modulePort.Name
						usedModuleOutputPorts[modulePort.Name] = true
						foundMatch = true
						break
					}
				}
			}
		}

		// 3. If no match found by any means, create a new internal signal
		if !foundMatch {
			newSignalName := fmt.Sprintf("inj_%s_%d", strings.ToLower(port.Name), rand.Intn(1000))
			newSignalObj := verilog.Port{
				Name:      newSignalName,
				Type:      port.Type,
				Width:     port.Width,
				IsSigned:  port.IsSigned,
				Direction: verilog.INTERNAL,
			}
			newDeclarations = append(newDeclarations, newSignalObj)
			portConnections[port.Name] = newSignalName
		}
	}

	return portConnections, newDeclarations, nil
}

func findMatchingVariable(
	port verilog.Port,
	variables []*verilog.Variable,
	usedVars map[string]bool,
) *verilog.Variable {
	for _, variable := range variables {
		if !usedVars[variable.Name] && variable.Type == port.Type && variable.Width == port.Width {
			return variable
		}
	}
	return nil
}

func generateSignalDeclaration(port verilog.Port, signalName string) string {
	widthStr := ""
	if port.Width > 1 {
		widthStr = fmt.Sprintf("[%d:0] ", port.Width-1)
	}
	signedStr := ""
	if port.IsSigned {
		signedStr = "signed "
	}
	return fmt.Sprintf("logic %s%s%s;", signedStr, widthStr, signalName)
}

func ensureOutputPortForSnippet(
	module *verilog.Module,
	snippet *Snippet,
	portConnections map[string]string,
	newDeclarations []verilog.Port,
) error {
	for _, port := range snippet.Module.Ports {
		if port.Direction == verilog.OUTPUT {
			if _, exists := portConnections[port.Name]; !exists {
				newPort := verilog.Port{
					Name:      fmt.Sprintf("inj_output_%s", strings.ToLower(port.Name)),
					Direction: verilog.OUTPUT,
					Type:      port.Type,
					Width:     port.Width,
					IsSigned:  port.IsSigned,
				}
				module.Ports = append(module.Ports, newPort)
				portConnections[port.Name] = newPort.Name
			}
		}
	}
	return nil
}

func generateSnippetInstantiation(snippet *Snippet, portConnections map[string]string) string {
	instanceName := fmt.Sprintf("%s_inst_%d", snippet.Name, rand.Intn(10000))
	instantiation := fmt.Sprintf("%s %s (\n", snippet.Module.Name, instanceName)

	connectionLines := []string{}
	for portName, signalName := range portConnections {
		connectionLines = append(connectionLines, fmt.Sprintf("    .%s(%s)", portName, signalName))
	}
	instantiation += strings.Join(connectionLines, ",\n")
	instantiation += "\n);"

	return instantiation
}

func insertSnippetIntoModule(
	module *verilog.Module,
	instantiation string,
	newDeclarations []verilog.Port,
) (string, error) {
	lines := strings.Split(module.Body, "\n")
	insertionIndex := findInsertionPoint(lines)

	for _, portToDeclare := range newDeclarations {
		declarationString := generateSignalDeclaration(portToDeclare, portToDeclare.Name)
		lines = append(
			lines[:insertionIndex],
			append([]string{declarationString}, lines[insertionIndex:]...)...)
		insertionIndex++
	}

	lines = append(
		lines[:insertionIndex],
		append([]string{instantiation}, lines[insertionIndex:]...)...)

	return strings.Join(lines, "\n"), nil
}

func findInsertionPoint(lines []string) int {
	for i, line := range lines {
		if strings.Contains(line, "endmodule") {
			return i
		}
	}
	return len(lines)
}

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

func MutateFile(fileName string) error {
	originalContent, err := utils.ReadFileContent(fileName)
	if err != nil {
		return fmt.Errorf("failed to read file %s: %v", fileName, err)
	}

	vsFile, err := verilog.ParseVerilog(originalContent)
	if err != nil {
		return fmt.Errorf("failed to parse file %s: %v", fileName, err)
	}

	for _, module := range vsFile.Modules {

		snippet, err := getRandomSnippet()
		if err != nil {
			return fmt.Errorf("failed to get snippet for mutation: %v", err)
		}

		var mutatedContent string
		mutationType := 0

		if mutationType == 0 {
			fmt.Println("Attempting InjectSnippet mutation...")
			mutatedContent, err = injectSnippetInModule(module, snippet)
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
	}
	return nil
}
