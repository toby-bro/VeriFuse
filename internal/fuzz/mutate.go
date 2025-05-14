package fuzz

import (
	"errors"
	"fmt"
	"math/rand"
	"os"
	"path/filepath"
	"strings"

	"github.com/toby-bro/pfuzz/internal/verilog"
	"github.com/toby-bro/pfuzz/pkg/utils"
)

var (
	snippets     = []*Snippet{}
	verilogFiles = []*verilog.VerilogFile{}
	logger       *utils.DebugLogger
	verbose      int
)

type Snippet struct {
	Name       string
	Module     *verilog.Module
	ParentFile *verilog.VerilogFile
}

func loadLogger(v int) {
	if logger == nil {
		logger = utils.NewDebugLogger(v)
	}
}

func findSnippetFiles() ([]string, error) {
	repoRoot, err := utils.GetRootDir()
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
	logger.Debug("Loading snippets from directory: %s", snippetsDir)
	if err != nil {
		return nil, err
	}
	return sourceFiles, nil
}

func loadSnippets() error {
	sourceFiles, err := findSnippetFiles()
	if err != nil {
		return fmt.Errorf("failed to find snippet files: %v", err)
	}
	for _, snippetFile := range sourceFiles {
		fileContent, err := utils.ReadFileContent(snippetFile)
		if err != nil {
			return fmt.Errorf("failed to read snippet file %s: %v", snippetFile, err)
		}
		verilogFile, err := verilog.ParseVerilog(fileContent, verbose)
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
	logger.Debug("Loaded %d snippets from %d files\n", len(snippets), len(sourceFiles))
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

func injectSnippetInModule(targetModule *verilog.Module, snippet *Snippet) error {
	// TODO: #18 exclude variables that are not in scope (zB function / task ...)
	variables, _, err := verilog.ParseVariables(snippet.ParentFile, targetModule.Body)
	if err != nil {
		return fmt.Errorf("failed to extract variables from module: %v", err)
	}

	portConnections, newSignalDeclarations, err := matchVariablesToSnippetPorts(
		targetModule,
		snippet,
		variables,
	)
	if err != nil {
		return fmt.Errorf("failed to match variables to snippet ports: %v", err)
	}

	// ensureOutputPortForSnippet modifies targetModule.Ports directly
	err = ensureOutputPortForSnippet(targetModule, snippet, portConnections)
	if err != nil {
		return fmt.Errorf("failed to ensure output port for snippet: %v", err)
	}

	instantiation := generateSnippetInstantiation(snippet, portConnections)

	// insertSnippetIntoModule modifies targetModule.Body directly
	err = insertSnippetIntoModule(targetModule, instantiation, newSignalDeclarations)
	if err != nil {
		return fmt.Errorf("failed to insert snippet into module: %v", err)
	}

	return nil
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
) error {
	for _, port := range snippet.Module.Ports {
		if port.Direction == verilog.OUTPUT {
			if _, exists := portConnections[port.Name]; !exists {
				newPort := verilog.Port{
					Name:      "inj_output_" + strings.ToLower(port.Name),
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
) error {
	lines := strings.Split(module.Body, "\n")
	insertionIndex := findInsertionPoint(lines)

	// Insert new signal declarations
	for i := len(newDeclarations) - 1; i >= 0; i-- { // Insert in reverse to maintain order at insertion point
		portToDeclare := newDeclarations[i]
		declarationString := generateSignalDeclaration(portToDeclare, portToDeclare.Name)
		lines = append(
			lines[:insertionIndex],
			append([]string{declarationString}, lines[insertionIndex:]...)...)
	}

	// Insert snippet instantiation
	instantiationInsertionIndex := insertionIndex + len(newDeclarations)
	lines = append(
		lines[:instantiationInsertionIndex],
		append([]string{instantiation}, lines[instantiationInsertionIndex:]...)...)

	module.Body = strings.Join(lines, "\n")
	return nil
}

func findInsertionPoint(lines []string) int {
	for i, line := range lines {
		if strings.Contains(line, "endmodule") {
			return i
		}
	}
	return len(lines)
}

func AddCodeToSnippet(originalContent, snippet string) (string, error) { //nolint:revive
	return "", errors.New("AddCodeToSnippet not implemented yet")
}

// dfsDependencies recursively adds child structs/classes of nodeName from parentVF into targetFile
// and records them under targetFile.DependancyMap[snippetName].DependsOn.
func dfsDependencies(
	nodeName string,
	parentVF *verilog.VerilogFile,
	targetFile *verilog.VerilogFile,
) {
	parentNode, ok := parentVF.DependancyMap[nodeName]
	if !ok {
		return
	}

	for _, dep := range parentNode.DependsOn {
		if _, found := targetFile.DependancyMap[dep]; found {
			// already in targetFile, skip
			continue
		}
		targetFile.DependancyMap[dep] = parentVF.DependancyMap[dep]
		// copy struct if needed
		if s, found := parentVF.Structs[dep]; found {
			if _, exists := targetFile.Structs[dep]; !exists {
				targetFile.Structs[dep] = s
			}
		}
		// copy class if needed
		if c, found := parentVF.Classes[dep]; found {
			if _, exists := targetFile.Classes[dep]; !exists {
				targetFile.Classes[dep] = c
			}
		}
		// copy module if needed
		if m, found := parentVF.Modules[dep]; found {
			if _, exists := targetFile.Modules[dep]; !exists {
				targetFile.Modules[dep] = m
			}
		}
		// recurse
		dfsDependencies(dep, parentVF, targetFile)
	}
}

func addDependancies(targetFile *verilog.VerilogFile, snippet *Snippet) error {
	parentVF := snippet.ParentFile
	if parentVF == nil {
		return errors.New("snippet parent file is nil")
	}
	// ensure targetFile.DependancyMap exists
	if targetFile.DependancyMap == nil {
		targetFile.DependancyMap = make(map[string]*verilog.DependencyNode)
	}
	// Ensure snippet entry exists, but with no parents
	if _, ok := targetFile.DependancyMap[snippet.Name]; !ok {
		targetFile.DependancyMap[snippet.Name] = &verilog.DependencyNode{
			Name:      snippet.Module.Name,
			DependsOn: []string{},
		}
	}
	targetFile.Modules[snippet.Module.Name] = snippet.Module

	dfsDependencies(snippet.Name, parentVF, targetFile)

	return nil
}

func MutateFile(
	originalSvFile *verilog.VerilogFile,
	pathToWrite string,
	verbose int,
) (*verilog.VerilogFile, error) {
	svFile := originalSvFile.DeepCopy()
	fileName := svFile.Name
	mutatedOverall := false
	injectedSnippetParentFiles := make(map[string]*verilog.VerilogFile)
	loadLogger(verbose)

	for moduleName, currentModule := range svFile.Modules {
		moduleToMutate := currentModule.DeepCopy()
		if moduleToMutate == nil {
			logger.Warn("Failed to copy module %s for mutation, skipping.", moduleName)
			continue
		}

		snippet, err := getRandomSnippet()
		if err != nil {
			logger.Warn(
				"Failed to get snippet for module %s: %v. Skipping mutation for this module.",
				moduleName,
				err,
			)
			continue
		}
		if snippet == nil || snippet.Module == nil || snippet.ParentFile == nil {
			logger.Warn(
				"Selected snippet, its module, or its parent file is nil for module %s. Skipping.",
				moduleName,
			)
			continue
		}
		if snippet.ParentFile.Name == "" {
			logger.Warn(
				"Snippet ParentFile name is empty for snippet '%s'. Dependency merging might be affected.",
				snippet.Name,
			)
		}

		mutationType := 0

		if mutationType == 0 {
			logger.Debug(
				"Attempting InjectSnippet mutation for module %s in file %s...\n",
				moduleToMutate.Name,
				fileName,
			)
			err = injectSnippetInModule(moduleToMutate, snippet)
			if err != nil {
				logger.Info(
					"InjectSnippet failed for module %s: %v. Skipping mutation for this module.\n",
					moduleToMutate.Name,
					err,
				)
				continue
			}

			svFile.Modules[moduleName] = moduleToMutate
			err := addDependancies(svFile, snippet)
			if err != nil {
				return nil, fmt.Errorf(
					"failed to add dependencies for snippet %s: %v",
					snippet.Name,
					err,
				)
			}
			mutatedOverall = true
			logger.Debug(
				"Mutation applied to module %s in %s (Type: %d)\n",
				moduleToMutate.Name,
				fileName,
				mutationType,
			)

			// Key by snippet.Module.Name so we know exactly which module to DFS
			injectedSnippetParentFiles[snippet.Name] = snippet.ParentFile
		}
	}

	finalMutatedContent, err := verilog.PrintVerilogFile(svFile)
	if err != nil {
		return nil, fmt.Errorf(
			"failed to print Verilog file %s after mutation: %v",
			pathToWrite,
			err,
		)
	}

	err = utils.WriteFileContent(pathToWrite, finalMutatedContent)
	if err != nil {
		return nil, fmt.Errorf("failed to write mutated content to %s: %v", pathToWrite, err)
	}
	if mutatedOverall {
		logger.Info("Successfully mutated and rewrote file %s\n", pathToWrite)
	} else {
		logger.Warn("File %s rewritten (no mutations applied or all failed).\n", pathToWrite)
	}

	return svFile, nil
}
