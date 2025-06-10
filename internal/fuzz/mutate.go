package fuzz

import (
	"errors"
	"fmt"
	"math/rand"
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

func injectSnippetInModule(targetModule *verilog.Module, snippet *snippets.Snippet) error {
	_, scopeTree, err := verilog.ParseVariables(
		snippet.ParentFile,
		targetModule.Body,
		targetModule.Parameters,
	)
	if err != nil {
		return fmt.Errorf("failed to extract variables from module: %v", err)
	}
	if scopeTree == nil {
		return fmt.Errorf("failed to parse scope tree for module %s", targetModule.Name)
	}

	bestScope := findBestScopeNode(scopeTree, snippet.Module.Ports)
	if bestScope == nil {
		logger.Warn(
			"Could not determine a best scope for snippet %s in module %s. Using module root.",
			snippet.Name,
			targetModule.Name,
		)
		bestScope = scopeTree
	}

	portConnections, newSignalDeclarations, err := matchVariablesToSnippetPorts(
		targetModule,
		snippet,
		scopeTree,
	)
	if err != nil {
		return fmt.Errorf("failed to match variables to snippet ports: %v", err)
	}

	logger.Debug(
		"Matched ports for snippet %s in module %s: %v",
		snippet.Name,
		targetModule.Name,
		portConnections,
	)

	err = ensureOutputPortForSnippet(targetModule, snippet, portConnections)
	if err != nil {
		return fmt.Errorf("failed to ensure output port for snippet: %v", err)
	}

	instantiation := generateSnippetInstantiation(snippet, portConnections)

	err = insertSnippetIntoModule(
		targetModule,
		instantiation,
		newSignalDeclarations,
		bestScope,
		scopeTree,
	)
	if err != nil {
		return fmt.Errorf("failed to insert snippet into module: %v", err)
	}
	logger.Info(
		"Injected snippet %s into module %s",
		snippet.Name,
		targetModule.Name,
	)

	return nil
}

func matchVariablesToSnippetPorts(
	module *verilog.Module,
	snippet *snippets.Snippet,
	scopeTree *verilog.ScopeNode,
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
			"findBestScopeNode returned nil, falling back to module root scope for snippet %s",
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
				"Created new signal %s for port %s in snippet %s and AnsiStyle %t",
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

	return instantiation
}

func insertSnippetIntoModule(
	module *verilog.Module,
	instantiation string,
	newDeclarations []verilog.Port,
	bestScope *verilog.ScopeNode,
	moduleScopeTree *verilog.ScopeNode,
) error {
	lines := strings.Split(module.Body, "\n")

	insertionPoint := findEndOfModuleDeclarations(lines)

	if bestScope != nil && moduleScopeTree != nil && bestScope != moduleScopeTree {
		logger.Debug(
			"Snippet insertion is based on a nested scope (level %d), but current logic inserts new code at the module level (around line %d). True nested scope textual insertion would require enhancing ScopeNode with source mapping.",
			bestScope.Level,
			insertionPoint,
		)
	}

	var contentToInsert []string
	if !module.AnsiStyle {
		for i := len(newDeclarations) - 1; i >= 0; i-- {
			portToDeclare := newDeclarations[i]
			declarationString := generateSignalDeclaration(portToDeclare, portToDeclare.Name)
			contentToInsert = append([]string{declarationString}, contentToInsert...)
		}
	}
	module.Ports = append(module.Ports, newDeclarations...)
	contentToInsert = append(contentToInsert, instantiation)

	if insertionPoint < 0 {
		insertionPoint = 0
	}

	if insertionPoint > len(lines) {
		insertionPoint = len(lines)
	}

	var resultLines []string
	resultLines = append(resultLines, lines[:insertionPoint]...)
	resultLines = append(resultLines, contentToInsert...)
	resultLines = append(resultLines, lines[insertionPoint:]...)

	module.Body = strings.Join(resultLines, "\n")
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

func AddCodeToSnippet(originalContent, snippet string) (string, error) { //nolint:revive
	return "", errors.New("AddCodeToSnippet not implemented yet")
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

	for moduleName, currentModule := range svFile.DeepCopy().Modules {
		moduleToMutate := currentModule.DeepCopy()
		if moduleToMutate == nil {
			logger.Warn("Failed to copy module %s for mutation, skipping.", moduleName)
			continue
		}

		snippet, err := snippets.GetRandomSnippet(verbose)
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

		logger.Debug(
			"Attempting to inject snippet %s in module %s from file %s...",
			snippet.Name,
			moduleToMutate.Name,
			fileName,
		)
		err = injectSnippetInModule(moduleToMutate, snippet)
		if err != nil {
			logger.Info(
				"InjectSnippet failed for module %s: %v. Skipping mutation for this module.",
				moduleToMutate.Name,
				err,
			)
			continue
		}

		svFile.Modules[moduleName] = moduleToMutate
		err = snippets.AddDependencies(svFile, snippet)
		if err != nil {
			logger.Error(
				"Failed to add dependencies for snippet %s: %v. Continuing with mutation.",
				snippet.Name,
				err,
			)
		}
		mutatedOverall = true
		logger.Debug(
			"Mutation applied to module %s in %s",
			moduleToMutate.Name,
			fileName,
		)

		// Key by snippet.Module.Name so we know exactly which module to DFS
		injectedSnippetParentFiles[snippet.Name] = snippet.ParentFile
	}

	if !mutatedOverall {
		logger.Info(
			"No successful mutations applied to file %s. Writing original or partially modified content if other steps occurred.",
			pathToWrite,
		)
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
		logger.Debug("Successfully mutated and rewrote file %s", pathToWrite)
	} else {
		logger.Warn("File %s rewritten (no mutations applied or all failed).", pathToWrite)
	}

	return svFile, nil
}
