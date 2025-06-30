package fuzz

import (
	"fmt"
	"math/rand"
	"path/filepath"
	"regexp"
	"strings"

	"github.com/toby-bro/pfuzz/internal/snippets"
	"github.com/toby-bro/pfuzz/pkg/utils"
	"github.com/toby-bro/pfuzz/pkg/verilog"
	"golang.org/x/exp/maps"
)

var logger *utils.DebugLogger

func loadLogger(v int) {
	if logger == nil {
		logger = utils.NewDebugLogger(v)
	}
}

func injectSnippetInModule(
	targetModule *verilog.Module,
	targetFile *verilog.VerilogFile,
	snippet *snippets.Snippet,
	instantiate bool,
	workerDir string,
) error {
	scopeTree, err := verilog.GetScopeTree(
		targetFile,
		targetModule.Body,
		targetModule.Parameters,
		targetModule.Ports,
	)
	if err != nil {
		return fmt.Errorf("[%s] failed to extract variables from module: %v", workerDir, err)
	}
	if scopeTree == nil {
		return fmt.Errorf(
			"[%s] failed to parse scope tree for module %s",
			workerDir,
			targetModule.Name,
		)
	}

	bestScope := findBestScopeNode(scopeTree, snippet.Module.Ports)
	if bestScope == nil {
		logger.Warn(
			"[%s] Could not determine a best scope for snippet %s in module %s. Using module root.",
			workerDir,
			snippet.Name,
			targetModule.Name,
		)
		bestScope = scopeTree
	}

	portConnections, newSignalDeclarations, err := matchVariablesToSnippetPorts(
		targetModule,
		snippet,
		scopeTree,
		workerDir,
	)
	if err != nil {
		return fmt.Errorf("failed to match variables to snippet ports: %v", err)
	}

	logger.Debug(
		"[%s] Matched ports for snippet %s in module %s: %v",
		workerDir,
		snippet.Name,
		targetModule.Name,
		portConnections,
	)

	err = ensureOutputPortForSnippet(targetModule, snippet, portConnections)
	if err != nil {
		return fmt.Errorf("failed to ensure output port for snippet: %v", err)
	}

	var injection string
	if instantiate {
		injection = generateSnippetInstantiation(snippet, portConnections)
	} else {
		injection = generateSnippetInjection(snippet, portConnections)
		targetModule.Parameters = append(targetModule.Parameters, snippet.Module.Parameters...)
	}

	err = injectSnippetIntoModule(
		targetModule,
		injection,
		newSignalDeclarations,
		bestScope,
		workerDir,
	)
	if err != nil {
		return fmt.Errorf("failed to insert snippet into module: %v", err)
	}
	if instantiate {
		logger.Info(
			"[%s] Instantiated snippet %s into module %s",
			workerDir,
			snippet.Name,
			targetModule.Name,
		)
	} else {
		logger.Info(
			"[%s] Injected snippet %s into module %s",
			workerDir,
			snippet.Name,
			targetModule.Name,
		)
	}

	return nil
}

func matchVariablesToSnippetPorts(
	module *verilog.Module,
	snippet *snippets.Snippet,
	scopeTree *verilog.ScopeNode,
	debugWorkerDir string,
) (map[string]string, []verilog.Port, error) {
	portConnections := make(map[string]string)
	newDeclarations := []verilog.Port{}

	usedInternalVars := make(map[string]bool)
	usedModuleInputPorts := make(map[string]bool)
	usedModuleOutputPorts := make(map[string]bool)
	// Tracks module variable names (from scope or module ports) already connected to a snippet port
	overallAssignedModuleVarNames := make(map[string]bool)

	bestScopeForSnippet := findBestScopeNode(scopeTree, snippet.Module.Ports)
	if bestScopeForSnippet == nil {
		logger.Warn(
			"[%s] findBestScopeNode returned nil, falling back to module root scope for snippet %s",
			debugWorkerDir,
			snippet.Name,
		)
		bestScopeForSnippet = scopeTree
	}

	varsAccessibleInBestScope := collectAccessibleVars(bestScopeForSnippet)

	for _, port := range snippet.Module.Ports {
		foundMatch := false
		var connectedVarName string

		if len(varsAccessibleInBestScope) > 0 {
			matchedVarFromScope := findMatchingVariable(
				port,
				varsAccessibleInBestScope,
				usedInternalVars,
			)
			// Check if this variable name has already been assigned to another snippet port
			if matchedVarFromScope != nil &&
				!overallAssignedModuleVarNames[matchedVarFromScope.Name] {
				connectedVarName = matchedVarFromScope.Name
				portConnections[port.Name] = connectedVarName
				usedInternalVars[connectedVarName] = true              // Mark as used for this strategy
				overallAssignedModuleVarNames[connectedVarName] = true // Mark as globally assigned
				foundMatch = true
			}
		}

		if !foundMatch {
			if port.Direction == verilog.INPUT {
				for _, modulePort := range module.Ports {
					if modulePort.Direction == verilog.INPUT &&
						modulePort.Type == port.Type &&
						modulePort.Width == port.Width &&
						!usedModuleInputPorts[modulePort.Name] && // Ensure this module input port isn't already used by this strategy
						!overallAssignedModuleVarNames[modulePort.Name] { // Ensure this module port name isn't globally assigned
						connectedVarName = modulePort.Name
						portConnections[port.Name] = connectedVarName
						usedModuleInputPorts[connectedVarName] = true          // Mark as used for this strategy
						overallAssignedModuleVarNames[connectedVarName] = true // Mark as globally assigned
						foundMatch = true
						break
					}
				}
			} else if port.Direction == verilog.OUTPUT {
				for _, modulePort := range module.Ports {
					if modulePort.Direction == verilog.OUTPUT &&
						modulePort.Type == port.Type &&
						modulePort.Width == port.Width &&
						!usedModuleOutputPorts[modulePort.Name] && // Ensure this module output port isn't already used by this strategy
						!overallAssignedModuleVarNames[modulePort.Name] { // Ensure this module port name isn't globally assigned
						connectedVarName = modulePort.Name
						portConnections[port.Name] = connectedVarName
						usedModuleOutputPorts[connectedVarName] = true         // Mark as used for this strategy
						overallAssignedModuleVarNames[connectedVarName] = true // Mark as globally assigned
						foundMatch = true
						break
					}
				}
			}
		}

		if !foundMatch {
			newSignalName := fmt.Sprintf("inj_%s_%d", strings.ToLower(port.Name), rand.Intn(1000))
			newSignalObj := verilog.Port{
				Name:            newSignalName,
				Type:            port.Type,
				Width:           port.Width,
				IsSigned:        port.IsSigned,
				Direction:       port.Direction,
				AlreadyDeclared: !module.AnsiStyle,
			}
			newDeclarations = append(newDeclarations, newSignalObj)
			portConnections[port.Name] = newSignalName
			// module.Ports = append(module.Ports, newSignalObj)
			logger.Debug(
				"[%s] Created new signal %s for port %s in snippet %s and AnsiStyle %t",
				debugWorkerDir,
				newSignalName,
				port.Name,
				snippet.Name,
				module.AnsiStyle,
			)
			// Newly created signals are unique by generation and don't need to be added to overallAssignedModuleVarNames
		}
	}

	return portConnections, newDeclarations, nil
}

func findBestScopeNode(
	rootNode *verilog.ScopeNode,
	requiredPorts []verilog.Port,
) *verilog.ScopeNode {
	if rootNode == nil {
		return nil
	}
	bestScope := rootNode
	maxSatisfiedCount := -1
	var perfectMatchScope *verilog.ScopeNode

	var dfs func(currentNode *verilog.ScopeNode, parentAccessibleVars map[string]*verilog.Variable)
	dfs = func(currentNode *verilog.ScopeNode, parentAccessibleVars map[string]*verilog.Variable) {
		if perfectMatchScope != nil {
			return
		}

		currentScopeAndParentVars := make(
			map[string]*verilog.Variable,
		)
		maps.Copy(currentScopeAndParentVars, currentNode.Variables)
		maps.Copy(currentScopeAndParentVars, parentAccessibleVars)

		tempUsedInCheck := make(map[string]bool)
		currentSatisfied := 0
		allRequiredSatisfied := true

		if len(requiredPorts) == 0 {
			perfectMatchScope = currentNode
			maxSatisfiedCount = 0
			bestScope = currentNode
			return
		}

		for _, port := range requiredPorts {
			portIsSatisfied := false
			for _, v := range currentScopeAndParentVars {
				if !tempUsedInCheck[v.Name] && v.Type == port.Type && v.Width == port.Width {
					currentSatisfied++
					tempUsedInCheck[v.Name] = true
					portIsSatisfied = true
					break
				}
			}
			if !portIsSatisfied {
				allRequiredSatisfied = false
			}
		}

		if allRequiredSatisfied {
			perfectMatchScope = currentNode
			maxSatisfiedCount = currentSatisfied
			bestScope = currentNode
			return
		}

		if currentSatisfied > maxSatisfiedCount {
			maxSatisfiedCount = currentSatisfied
			bestScope = currentNode
		}

		varsForChildren := make(
			map[string]*verilog.Variable,
		)
		maps.Copy(varsForChildren, currentNode.Variables)
		maps.Copy(
			varsForChildren,
			parentAccessibleVars,
		)

		for _, child := range currentNode.Children {
			dfs(child, varsForChildren)
			if perfectMatchScope != nil {
				return
			}
		}
	}

	dfs(rootNode, make(map[string]*verilog.Variable))

	if perfectMatchScope != nil {
		return perfectMatchScope
	}
	return bestScope
}

func collectAccessibleVars(node *verilog.ScopeNode) map[string]*verilog.Variable {
	collectedVars := make(map[string]*verilog.Variable)
	curr := node
	for curr != nil {
		maps.Copy(collectedVars, curr.Variables)
		curr = curr.Parent
	}
	return collectedVars
}

func findMatchingVariable(
	port verilog.Port,
	variables map[string]*verilog.Variable,
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
	directionStr := ""
	switch port.Direction {
	case verilog.INPUT:
		directionStr = "input "
	case verilog.OUTPUT:
		directionStr = "output "
	case verilog.INOUT:
		directionStr = "inout "
	case verilog.INTERNAL:
		directionStr = ""
	}

	typeStr := port.Type.String()
	if typeStr == "" {
		typeStr = "logic" // fallback
	}

	return fmt.Sprintf("%s%s %s%s%s;", directionStr, typeStr, signedStr, widthStr, signalName)
}

func ensureOutputPortForSnippet(
	module *verilog.Module,
	snippet *snippets.Snippet,
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

// This function replaces the port names in the snippet string with the corresponding signal names
// from the portConnection map. It returns the modified snippet string.
func replacePortNames(snippetString string, portConnection map[string]string) string {
	for portName, signalName := range portConnection {
		re := regexp.MustCompile(`\b` + regexp.QuoteMeta(portName) + `\b`)
		snippetString = re.ReplaceAllString(snippetString, signalName)
	}
	return snippetString
}

// This function changes the names of the port variables in the snippet to match the names given in portConnections
// It returns a string that can be directly injected into any other module at the given scope level.
func generateSnippetInjection(
	snippet *snippets.Snippet,
	portConnections map[string]string,
) string {
	snippetString := snippet.Module.Body
	snippetString = replacePortNames(snippetString, portConnections)
	snippetString = utils.TrimEmptyLines(snippetString)
	snippetString = fmt.Sprintf(
		"    // BEGIN: %s\n%s\n    // END: %s\n",
		strings.TrimSpace(snippet.Name),
		snippetString,
		strings.TrimSpace(snippet.Name),
	)

	return snippetString
}

func generateSnippetInstantiation(
	snippet *snippets.Snippet,
	portConnections map[string]string,
) string {
	instanceName := fmt.Sprintf("%s_inst_%d", snippet.Name, rand.Intn(10000))
	instantiation := fmt.Sprintf("%s %s (\n", snippet.Module.Name, instanceName)

	connectionLines := []string{}
	for portName, signalName := range portConnections {
		connectionLines = append(connectionLines, fmt.Sprintf("    .%s(%s)", portName, signalName))
	}
	instantiation += strings.Join(connectionLines, ",\n")
	instantiation += "\n);"

	return utils.Indent(instantiation)
}

func insertTextAtLine(module *verilog.Module, text string, line int, indentLevel int) error {
	lines := strings.Split(module.Body, "\n")
	if line < 0 || line > len(lines) {
		return fmt.Errorf("line number %d is out of bounds for module %s", line, module.Name)
	}

	for range indentLevel {
		text = utils.Indent(text)
	}
	textLines := strings.Split(text, "\n")

	lines = append(lines[:line], append(textLines, lines[line:]...)...)
	module.Body = strings.Join(lines, "\n")

	return nil
}

func injectSnippetIntoModule(
	module *verilog.Module,
	instantiation string,
	newDeclarations []verilog.Port,
	bestScope *verilog.ScopeNode,
	debugWorkerDir string,
) error {
	// Determine the insertion line based on the best scope's LastLine
	var insertionLine int
	if bestScope != nil && bestScope.LastLine > -1 {
		// Insert after the last line where a variable was declared in this scope
		insertionLine = bestScope.LastLine + 1
		logger.Debug(
			"[%s] Using scope-based insertion at line %d (scope level %d)",
			debugWorkerDir,
			insertionLine,
			bestScope.Level,
		)
	} else {
		// Fallback to the old method
		lines := strings.Split(module.Body, "\n")
		insertionLine = findEndOfModuleDeclarations(lines)
		logger.Debug(
			"[%s] Using fallback insertion at line %d (no best scope found)",
			debugWorkerDir,
			insertionLine,
		)
	}

	// Add new signal declarations first (if needed)
	if !module.AnsiStyle {
		for i := len(newDeclarations) - 1; i >= 0; i-- {
			portToDeclare := newDeclarations[i]
			declarationString := generateSignalDeclaration(portToDeclare, portToDeclare.Name)
			err := insertTextAtLine(module, declarationString, insertionLine, bestScope.Level)
			if err != nil {
				return fmt.Errorf("failed to insert signal declaration: %v", err)
			}
			// Increment insertion line for next declaration
			insertionLine++
		}
	}
	logger.Debug(
		"[%s] Inserted %d new signal declarations at line %d in module %s",
		debugWorkerDir,
		len(newDeclarations),
		insertionLine,
		module.Name,
	)

	// Add the new ports to the module
	module.Ports = append(module.Ports, newDeclarations...)

	// Insert the snippet instantiation/injection
	err := insertTextAtLine(module, instantiation, insertionLine, bestScope.Level)
	if err != nil {
		return fmt.Errorf("failed to insert snippet: %v", err)
	}

	return nil
}

func findEndOfModuleDeclarations(lines []string) int {
	lastDeclarationLine := -1
	for i, line := range lines {
		trimmedLine := strings.TrimSpace(line)

		if strings.HasPrefix(trimmedLine, "//") || trimmedLine == "" {
			continue
		}

		if strings.HasPrefix(trimmedLine, "assign ") ||
			strings.HasPrefix(trimmedLine, "always") ||
			strings.HasPrefix(trimmedLine, "initial ") ||
			strings.HasPrefix(trimmedLine, "generate") ||
			(strings.Contains(trimmedLine, "(") && !isDeclarationLine(trimmedLine) &&
				!strings.HasPrefix(trimmedLine, "function ") &&
				!strings.HasPrefix(trimmedLine, "task ") &&
				!strings.HasPrefix(trimmedLine, "module ")) {
			if lastDeclarationLine != -1 {
				return lastDeclarationLine + 1
			}
			return i
		}

		if isDeclarationLine(trimmedLine) {
			lastDeclarationLine = i
		}

		if strings.HasPrefix(trimmedLine, "endmodule") {
			if lastDeclarationLine != -1 {
				return lastDeclarationLine + 1
			}
			return i
		}
	}

	if lastDeclarationLine != -1 {
		return lastDeclarationLine + 1
	}

	for i := len(lines) - 1; i >= 0; i-- {
		if strings.Contains(lines[i], "endmodule") {
			return i
		}
	}
	return len(lines)
}

func isDeclarationLine(line string) bool {
	trimmedLine := strings.TrimSpace(line)
	declarationKeywords := []string{
		"input", "output", "inout", "reg", "wire", "logic", "integer", "real", "time", "realtime",
		"bit", "byte", "shortint", "int", "longint", "shortreal", "string", "parameter", "localparam",
		"genvar", "typedef", "struct", "enum", "class",
	}
	for _, keyword := range declarationKeywords {
		if strings.HasPrefix(trimmedLine, keyword+" ") ||
			strings.HasPrefix(trimmedLine, keyword+"[") {
			return true
		}
	}
	if !strings.Contains(trimmedLine, "(") && strings.HasSuffix(trimmedLine, ";") &&
		strings.Count(trimmedLine, " ") >= 1 {
		if !strings.ContainsAny(strings.Split(trimmedLine, " ")[0], "=+-*/%&|^<>()[]{}:;") {
			return true
		}
	}
	return false
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

	workerDir := filepath.Base(filepath.Dir(pathToWrite))

	for {
		for moduleName, currentModule := range svFile.Modules {
			if len(svFile.DependencyMap[moduleName].DependedBy) > 0 {
				logger.Debug(
					"[%s] Skipping module %s due to dependencies: %v",
					workerDir,
					moduleName,
					svFile.DependencyMap[moduleName].DependedBy,
				)
				continue
			}

			moduleToMutate := currentModule.DeepCopy()
			if moduleToMutate == nil {
				logger.Warn(
					"[%s] Failed to copy module %s for mutation, skipping.",
					workerDir,
					moduleName,
				)
				continue
			}

			snippet, err := snippets.GetRandomSnippet(verbose)
			if err != nil {
				logger.Warn(
					"[%s] Failed to get snippet for module %s: %v. Skipping mutation for this module.",
					workerDir,
					moduleName,
					err,
				)
				continue
			}
			if snippet == nil || snippet.Module == nil || snippet.ParentFile == nil {
				logger.Warn(
					"[%s] Selected snippet, its module, or its parent file is nil for module %s. Skipping.",
					workerDir,
					moduleName,
				)
				continue
			}
			if snippet.ParentFile.Name == "" {
				logger.Warn(
					"[%s] Snippet ParentFile name is empty for snippet '%s'. Dependency merging might be affected.",
					workerDir,
					snippet.Name,
				)
			}

			logger.Debug(
				"[%s] Attempting to inject snippet %s in module %s from file %s...",
				workerDir,
				snippet.Name,
				moduleToMutate.Name,
				fileName,
			)
			instantiate := rand.Intn(3) == 0
			err = injectSnippetInModule(
				moduleToMutate,
				svFile,
				snippet,
				instantiate,
				workerDir,
			)
			if err != nil {
				logger.Info(
					"[%s] InjectSnippet failed for module %s: %v. Skipping mutation for this module.",
					workerDir,
					moduleToMutate.Name,
					err,
				)
				continue
			}

			svFile.Modules[moduleName] = moduleToMutate

			err = snippets.GeneralAddDependencies(svFile, snippet, instantiate)
			if err != nil {
				logger.Error(
					"[%s] Failed to add dependencies for snippet %s: %v. Continuing with mutation.",
					workerDir,
					snippet.Name,
					err,
				)
			}

			logger.Debug(
				"[%s] Successfully injected snippet %s into module %s",
				workerDir,
				snippet.Name,
				moduleToMutate.Name,
			)

			if instantiate {
				svFile.AddDependency(
					moduleToMutate.Name,
					snippet.Module.Name,
				)
			} else {
				svFile.AddDependency(
					moduleToMutate.Name,
					snippet.ParentFile.DependencyMap[snippet.Name].DependsOn...,
				)
			}

			mutatedOverall = true
			logger.Debug(
				"[%s] Mutation applied to module %s in %s",
				workerDir,
				moduleToMutate.Name,
				fileName,
			)

			// Key by snippet.Module.Name so we know exactly which module to DFS
			injectedSnippetParentFiles[snippet.Name] = snippet.ParentFile
		}
		if rand.Intn(3) == 0 {
			break
		}
	}

	if !mutatedOverall {
		logger.Info(
			"[%s] No successful mutations applied to file %s. Writing original or partially modified content if other steps occurred.",
			workerDir,
			pathToWrite,
		)
	}

	finalMutatedContent, err := verilog.PrintVerilogFile(svFile)
	if err != nil {
		return nil, fmt.Errorf(
			"[%s] failed to print Verilog file %s after mutation: %v",
			workerDir,
			pathToWrite,
			err,
		)
	}

	err = utils.WriteFileContent(pathToWrite, finalMutatedContent)
	if err != nil {
		return nil, fmt.Errorf("failed to write mutated content to %s: %v", pathToWrite, err)
	}

	if mutatedOverall {
		logger.Debug("[%s] Successfully mutated and rewrote file %s", workerDir, pathToWrite)
	} else {
		logger.Warn("[%s] File %s rewritten (no mutations applied or all failed).", workerDir, pathToWrite)
	}

	return svFile, nil
}
